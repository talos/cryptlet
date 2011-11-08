/**
  * Gmail GPG :: A little bit 'o' privacy for Gmail in a bookmarklet.
  *
  * John Krauss 2011
  */

(function () {

	/*************** http://www.hanewin.net/encrypt/rsa.js *******************/

	/* RSA public key encryption/decryption
	 * The following functions are (c) 2000 by John M Hanna and are
	 * released under the terms of the Gnu Public License.
	 * You must freely redistribute them with their source -- see the
	 * GPL for details.
	 *  -- Latest version found at http://sourceforge.net/projects/shop-js
	 *
	 * Modifications and GnuPG multi precision integer (mpi) conversion added
	 * 2004 by Herbert Hanewinkel, www.haneWIN.de
	 */

	// --- Arbitrary Precision Math ---
	// badd(a,b), bsub(a,b), bsqr(a), bmul(a,b)
	// bdiv(a,b), bmod(a,b), bexpmod(g,e,m), bmodexp(g,e,m)

	// bs is the shift, bm is the mask
	// set single precision bits to 28
	var bs=28;
	var bx2=1<<bs, bm=bx2-1, bx=bx2>>1, bd=bs>>1, bdm=(1<<bd)-1;

	var log2=Math.log(2);

	function zeros(n)
	{
		var r=new Array(n);

		while(n-->0) r[n]=0;
		return r;
	}

	function zclip(r)
	{
		var n = r.length;
		if(r[n-1]) return r;
		while(n>1 && r[n-1]==0) n--;
		return r.slice(0,n);
	}

	// returns bit length of integer x
	function nbits(x)
	{
		var n = 1, t;
		if((t=x>>>16) != 0) { x = t; n += 16; }
		if((t=x>>8) != 0) { x = t; n += 8; }
		if((t=x>>4) != 0) { x = t; n += 4; }
		if((t=x>>2) != 0) { x = t; n += 2; }
		if((t=x>>1) != 0) { x = t; n += 1; }
		return n;
	}

	function badd(a,b)
	{
		var al=a.length;
		var bl=b.length;

		if(al < bl) return badd(b,a);

		var r=new Array(al);
		var c=0, n=0;

		for(; n<bl; n++)
		{
			c+=a[n]+b[n];
			r[n]=c & bm;
			c>>>=bs;
		}
		for(; n<al; n++)
		{
			c+=a[n];
			r[n]=c & bm;
			c>>>=bs;
		}
		if(c) r[n]=c;
		return r;
	}

	function bsub(a,b)
	{
		var al=a.length;
		var bl=b.length;

		if(bl > al) return [];
		if(bl == al)
		{
			if(b[bl-1] > a[bl-1]) return [];
			if(bl==1) return [a[0]-b[0]];
		}

		var r=new Array(al);
		var c=0;

		for(var n=0; n<bl; n++)
		{
			c+=a[n]-b[n];
			r[n]=c & bm;
			c>>=bs;
		}
		for(;n<al; n++)
		{
			c+=a[n];
			r[n]=c & bm;
			c>>=bs;
		}
		if(c) return [];

		return zclip(r);
	}

	function ip(w, n, x, y, c)
	{
		var xl = x&bdm;
		var xh = x>>bd;

		var yl = y&bdm;
		var yh = y>>bd;

		var m = xh*yl+yh*xl;
		var l = xl*yl+((m&bdm)<<bd)+w[n]+c;
		w[n] = l&bm;
		c = xh*yh+(m>>bd)+(l>>bs);
		return c;
	}

	// Multiple-precision squaring, HAC Algorithm 14.16

	function bsqr(x)
	{
		var t = x.length;
		var n = 2*t;
		var r = zeros(n);
		var c = 0;
		var i, j;

		for(i = 0; i < t; i++)
		{
			c = ip(r,2*i,x[i],x[i],0);
			for(j = i+1; j < t; j++)
			{
				c = ip(r,i+j,2*x[j],x[i],c);
			}
			r[i+t] = c;
		}

		return zclip(r);
	}

	// Multiple-precision multiplication, HAC Algorithm 14.12

	function bmul(x,y)
	{
		var n = x.length;
		var t = y.length;
		var r = zeros(n+t-1);
		var c, i, j;

		for(i = 0; i < t; i++)
		{
			c = 0;
			for(j = 0; j < n; j++)
			{
				c = ip(r,i+j,x[j],y[i],c);
			}
			r[i+n] = c;
		}

		return zclip(r);
	}

	function toppart(x,start,len)
	{
		var n=0;
		while(start >= 0 && len-->0) n=n*bx2+x[start--];
		return n;
	}

	// Multiple-precision division, HAC Algorithm 14.20

	function bdiv(a,b)
	{
		var n=a.length-1;
		var t=b.length-1;
		var nmt=n-t;

		// trivial cases; a < b
		if(n < t || n==t && (a[n]<b[n] || n>0 && a[n]==b[n] && a[n-1]<b[n-1]))
		{
			this.q=[0]; this.mod=a;
			return this;
		}

		// trivial cases; q < 4
		if(n==t && toppart(a,t,2)/toppart(b,t,2) <4)
		{
			var x=a.concat();
			var qq=0;
			var xx;
			for(;;)
			{
				xx=bsub(x,b);
				if(xx.length==0) break;
				x=xx; qq++;
			}
			this.q=[qq]; this.mod=x;
			return this;
		}

		// normalize
		var shift2=Math.floor(Math.log(b[t])/log2)+1;
		var shift=bs-shift2;

		var x=a.concat();
		var y=b.concat();

		if(shift)
		{
			for(i=t; i>0; i--) y[i]=((y[i]<<shift) & bm) | (y[i-1] >> shift2);
			y[0]=(y[0]<<shift) & bm;
			if(x[n] & ((bm <<shift2) & bm))
			{
				x[++n]=0; nmt++;
			}
			for(i=n; i>0; i--) x[i]=((x[i]<<shift) & bm) | (x[i-1] >> shift2);
			x[0]=(x[0]<<shift) & bm;
		}

		var i, j, x2;
		var q=zeros(nmt+1);
		var y2=zeros(nmt).concat(y);
		for(;;)
		{
			x2=bsub(x,y2);
			if(x2.length==0) break;
			q[nmt]++;
			x=x2;
		}

		var yt=y[t], top=toppart(y,t,2)
		for(i=n; i>t; i--)
		{
			var m=i-t-1;
			if(i >= x.length) q[m]=1;
			else if(x[i] == yt) q[m]=bm;
			else q[m]=Math.floor(toppart(x,i,2)/yt);

			var topx=toppart(x,i,3);
			while(q[m] * top > topx) q[m]--;

			//x-=q[m]*y*b^m
			y2=y2.slice(1);
			x2=bsub(x,bmul([q[m]],y2));
			if(x2.length==0)
			{
				q[m]--;
				x2=bsub(x,bmul([q[m]],y2));
			}
			x=x2;
		}
		// de-normalize
		if(shift)
		{
			for(i=0; i<x.length-1; i++) x[i]=(x[i]>>shift) | ((x[i+1] << shift2) & bm);
			x[x.length-1]>>=shift;
		}

		this.q = zclip(q);
		this.mod = zclip(x);
		return this;
	}

	function simplemod(i,m) // returns the mod where m < 2^bd
	{
		var c=0, v;
		for(var n=i.length-1; n>=0; n--)
		{
			v=i[n];
			c=((v >> bd) + (c<<bd)) % m;
			c=((v & bdm) + (c<<bd)) % m;
		}
		return c;
	}

	function bmod(p,m)
	{
		if(m.length==1)
		{
			if(p.length==1) return [p[0] % m[0]];
			if(m[0] < bdm) return [simplemod(p,m[0])];
		}

		var r=bdiv(p,m);
		return r.mod;
	}

	// Barrett's modular reduction, HAC Algorithm 14.42

	function bmod2(x,m,mu)
	{
		var xl=x.length - (m.length << 1);
		if(xl > 0) return bmod2(x.slice(0,xl).concat(bmod2(x.slice(xl),m,mu)),m,mu);

		var ml1=m.length+1, ml2=m.length-1,rr;
		//var q1=x.slice(ml2)
		//var q2=bmul(q1,mu)
		var q3=bmul(x.slice(ml2),mu).slice(ml1);
		var r1=x.slice(0,ml1);
		var r2=bmul(q3,m).slice(0,ml1);
		var r=bsub(r1,r2);
		
		if(r.length==0)
		{
			r1[ml1]=1;
			r=bsub(r1,r2);
		}
		for(var n=0;;n++)
		{
			rr=bsub(r,m);
			if(rr.length==0) break;
			r=rr;
			if(n>=3) return bmod2(r,m,mu);
		}
		return r;
	}

	// Modular exponentiation, HAC Algorithm 14.79

	function bexpmod(g,e,m)
	{
		var a = g.concat();
		var l = e.length-1;
		var n = nbits(e[l])-2;

		for(; l >= 0; l--)
		{
			for(; n >= 0; n-=1)
			{
				a=bmod(bsqr(a),m);
				if(e[l] & (1<<n)) a=bmod(bmul(a,g),m);
			}
			n = bs-1;
		}
		return a;
	}

	// Modular exponentiation using Barrett reduction

	function bmodexp(g,e,m)
	{
		var a=g.concat();
		var l=e.length-1;
		var n=m.length*2;
		var mu=zeros(n+1);
		mu[n]=1;
		mu=bdiv(mu,m).q;

		n = nbits(e[l])-2;

		for(; l >= 0; l--)
		{
			for(; n >= 0; n-=1)
			{
				a=bmod2(bsqr(a),m, mu);
				if(e[l] & (1<<n)) a=bmod2(bmul(a,g),m, mu);
			}
			n = bs-1;
		}
		return a;
	}

	// -----------------------------------------------------
	// Compute s**e mod m for RSA public key operation

	function RSAencrypt(s, e, m) { return bexpmod(s,e,m); }

	// Compute m**d mod p*q for RSA private key operations.

	function RSAdecrypt(m, d, p, q, u)
	{
		var xp = bmodexp(bmod(m,p), bmod(d,bsub(p,[1])), p);
		var xq = bmodexp(bmod(m,q), bmod(d,bsub(q,[1])), q);

		var t=bsub(xq,xp);
		if(t.length==0)
		{
			t=bsub(xp,xq);
			t=bmod(bmul(t, u), q);
			t=bsub(q,t);
		}
		else
		{
			t=bmod(bmul(t, u), q);
		} 
		return badd(bmul(t,p), xp);
	}

	// -----------------------------------------------------------------
	// conversion functions: num array <-> multi precision integer (mpi)
	// mpi: 2 octets with length in bits + octets in big endian order

	function mpi2b(s)
	{
		var bn=1, r=[0], rn=0, sb=256;
		var c, sn=s.length;
		if(sn < 2)
		{
			fail('string too short, not a MPI');
			return 0;
		}

		var len=(sn-2)*8;
		var bits=s.charCodeAt(0)*256+s.charCodeAt(1);
		if(bits > len || bits < len-8) 
		{
			fail('not a MPI, bits='+bits+",len="+len);
			return 0;
		}

		for(var n=0; n<len; n++)
		{
			if((sb<<=1) > 255)
			{
				sb=1; c=s.charCodeAt(--sn);
			}
			if(bn > bm)
			{
				bn=1;
				r[++rn]=0;
			}
			if(c & sb) r[rn]|=bn;
			bn<<=1;
		}
		return r;
	}

	function b2mpi(b)
	{
		var bn=1, bc=0, r=[0], rb=1, rn=0;
		var bits=b.length*bs;
		var n, rr='';

		for(n=0; n<bits; n++)
		{
			if(b[bc] & bn) r[rn]|=rb;
			if((rb<<=1) > 255)
			{
				rb=1; r[++rn]=0;
			}
			if((bn<<=1) > bm)
			{
				bn=1; bc++;
			}
		}

		while(rn && r[rn]==0) rn--;

		bn=256;
		for(bits=8; bits>0; bits--) if(r[rn] & (bn>>=1)) break;
		bits+=rn*8;

		rr+=String.fromCharCode(bits/256)+String.fromCharCode(bits%256);
		if(bits) for(n=rn; n>=0; n--) rr+=String.fromCharCode(r[n]);
		return rr;
	}

	/*************** http://www.hanewin.net/encrypt/aes-enc.js *******************/
	
	/* Rijndael (AES) Encryption
	 * Copyright 2005 Herbert Hanewinkel, www.haneWIN.de
	 * version 1.1, check www.haneWIN.de for the latest version

	 * This software is provided as-is, without express or implied warranty.  
	 * Permission to use, copy, modify, distribute or sell this software, with or
	 * without fee, for any purpose and by any individual or organization, is hereby
	 * granted, provided that the above copyright notice and this paragraph appear 
	 * in all copies. Distribution as a part of an application or binary must
	 * include the above copyright notice in the documentation and/or other
	 * materials provided with the application or distribution.
	 */

	// The round constants used in subkey expansion
	var Rcon = [ 
		0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 
		0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 
		0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91 ];

	// Precomputed lookup table for the SBox
	var S = [
		99, 124, 119, 123, 242, 107, 111, 197,  48,   1, 103,  43, 254, 215, 171, 
		118, 202, 130, 201, 125, 250,  89,  71, 240, 173, 212, 162, 175, 156, 164, 
		114, 192, 183, 253, 147,  38,  54,  63, 247, 204,  52, 165, 229, 241, 113, 
		216,  49,  21,   4, 199,  35, 195,  24, 150,   5, 154,   7,  18, 128, 226, 
		235,  39, 178, 117,   9, 131,  44,  26,  27, 110,  90, 160,  82,  59, 214, 
		179,  41, 227,  47, 132,  83, 209,   0, 237,  32, 252, 177,  91, 106, 203, 
		190,  57,  74,  76,  88, 207, 208, 239, 170, 251,  67,  77,  51, 133,  69, 
		249,   2, 127,  80,  60, 159, 168,  81, 163,  64, 143, 146, 157,  56, 245, 
		188, 182, 218,  33,  16, 255, 243, 210, 205,  12,  19, 236,  95, 151,  68,  
		23,  196, 167, 126,  61, 100,  93,  25, 115,  96, 129,  79, 220,  34,  42, 
		144, 136,  70, 238, 184,  20, 222,  94,  11, 219, 224,  50,  58,  10,  73,
		6,  36,  92, 194, 211, 172,  98, 145, 149, 228, 121, 231, 200,  55, 109, 
		141, 213,  78, 169, 108,  86, 244, 234, 101, 122, 174,   8, 186, 120,  37,  
		46,  28, 166, 180, 198, 232, 221, 116,  31,  75, 189, 139, 138, 112,  62, 
		181, 102,  72,   3, 246,  14,  97,  53,  87, 185, 134, 193,  29, 158, 225,
		248, 152,  17, 105, 217, 142, 148, 155,  30, 135, 233, 206,  85,  40, 223,
		140, 161, 137,  13, 191, 230,  66, 104,  65, 153,  45,  15, 176,  84, 187,  
		22 ];

	var T1 = [
		0xa56363c6, 0x847c7cf8, 0x997777ee, 0x8d7b7bf6,
		0x0df2f2ff, 0xbd6b6bd6, 0xb16f6fde, 0x54c5c591,
		0x50303060, 0x03010102, 0xa96767ce, 0x7d2b2b56,
		0x19fefee7, 0x62d7d7b5, 0xe6abab4d, 0x9a7676ec,
		0x45caca8f, 0x9d82821f, 0x40c9c989, 0x877d7dfa,
		0x15fafaef, 0xeb5959b2, 0xc947478e, 0x0bf0f0fb,
		0xecadad41, 0x67d4d4b3, 0xfda2a25f, 0xeaafaf45,
		0xbf9c9c23, 0xf7a4a453, 0x967272e4, 0x5bc0c09b,
		0xc2b7b775, 0x1cfdfde1, 0xae93933d, 0x6a26264c,
		0x5a36366c, 0x413f3f7e, 0x02f7f7f5, 0x4fcccc83,
		0x5c343468, 0xf4a5a551, 0x34e5e5d1, 0x08f1f1f9,
		0x937171e2, 0x73d8d8ab, 0x53313162, 0x3f15152a,
		0x0c040408, 0x52c7c795, 0x65232346, 0x5ec3c39d,
		0x28181830, 0xa1969637, 0x0f05050a, 0xb59a9a2f,
		0x0907070e, 0x36121224, 0x9b80801b, 0x3de2e2df,
		0x26ebebcd, 0x6927274e, 0xcdb2b27f, 0x9f7575ea,
		0x1b090912, 0x9e83831d, 0x742c2c58, 0x2e1a1a34,
		0x2d1b1b36, 0xb26e6edc, 0xee5a5ab4, 0xfba0a05b,
		0xf65252a4, 0x4d3b3b76, 0x61d6d6b7, 0xceb3b37d,
		0x7b292952, 0x3ee3e3dd, 0x712f2f5e, 0x97848413,
		0xf55353a6, 0x68d1d1b9, 0x00000000, 0x2cededc1,
		0x60202040, 0x1ffcfce3, 0xc8b1b179, 0xed5b5bb6,
		0xbe6a6ad4, 0x46cbcb8d, 0xd9bebe67, 0x4b393972,
		0xde4a4a94, 0xd44c4c98, 0xe85858b0, 0x4acfcf85,
		0x6bd0d0bb, 0x2aefefc5, 0xe5aaaa4f, 0x16fbfbed,
		0xc5434386, 0xd74d4d9a, 0x55333366, 0x94858511,
		0xcf45458a, 0x10f9f9e9, 0x06020204, 0x817f7ffe,
		0xf05050a0, 0x443c3c78, 0xba9f9f25, 0xe3a8a84b,
		0xf35151a2, 0xfea3a35d, 0xc0404080, 0x8a8f8f05,
		0xad92923f, 0xbc9d9d21, 0x48383870, 0x04f5f5f1,
		0xdfbcbc63, 0xc1b6b677, 0x75dadaaf, 0x63212142,
		0x30101020, 0x1affffe5, 0x0ef3f3fd, 0x6dd2d2bf,
		0x4ccdcd81, 0x140c0c18, 0x35131326, 0x2fececc3,
		0xe15f5fbe, 0xa2979735, 0xcc444488, 0x3917172e,
		0x57c4c493, 0xf2a7a755, 0x827e7efc, 0x473d3d7a,
		0xac6464c8, 0xe75d5dba, 0x2b191932, 0x957373e6,
		0xa06060c0, 0x98818119, 0xd14f4f9e, 0x7fdcdca3,
		0x66222244, 0x7e2a2a54, 0xab90903b, 0x8388880b,
		0xca46468c, 0x29eeeec7, 0xd3b8b86b, 0x3c141428,
		0x79dedea7, 0xe25e5ebc, 0x1d0b0b16, 0x76dbdbad,
		0x3be0e0db, 0x56323264, 0x4e3a3a74, 0x1e0a0a14,
		0xdb494992, 0x0a06060c, 0x6c242448, 0xe45c5cb8,
		0x5dc2c29f, 0x6ed3d3bd, 0xefacac43, 0xa66262c4,
		0xa8919139, 0xa4959531, 0x37e4e4d3, 0x8b7979f2,
		0x32e7e7d5, 0x43c8c88b, 0x5937376e, 0xb76d6dda,
		0x8c8d8d01, 0x64d5d5b1, 0xd24e4e9c, 0xe0a9a949,
		0xb46c6cd8, 0xfa5656ac, 0x07f4f4f3, 0x25eaeacf,
		0xaf6565ca, 0x8e7a7af4, 0xe9aeae47, 0x18080810,
		0xd5baba6f, 0x887878f0, 0x6f25254a, 0x722e2e5c,
		0x241c1c38, 0xf1a6a657, 0xc7b4b473, 0x51c6c697,
		0x23e8e8cb, 0x7cdddda1, 0x9c7474e8, 0x211f1f3e,
		0xdd4b4b96, 0xdcbdbd61, 0x868b8b0d, 0x858a8a0f,
		0x907070e0, 0x423e3e7c, 0xc4b5b571, 0xaa6666cc,
		0xd8484890, 0x05030306, 0x01f6f6f7, 0x120e0e1c,
		0xa36161c2, 0x5f35356a, 0xf95757ae, 0xd0b9b969,
		0x91868617, 0x58c1c199, 0x271d1d3a, 0xb99e9e27,
		0x38e1e1d9, 0x13f8f8eb, 0xb398982b, 0x33111122,
		0xbb6969d2, 0x70d9d9a9, 0x898e8e07, 0xa7949433,
		0xb69b9b2d, 0x221e1e3c, 0x92878715, 0x20e9e9c9,
		0x49cece87, 0xff5555aa, 0x78282850, 0x7adfdfa5,
		0x8f8c8c03, 0xf8a1a159, 0x80898909, 0x170d0d1a,
		0xdabfbf65, 0x31e6e6d7, 0xc6424284, 0xb86868d0,
		0xc3414182, 0xb0999929, 0x772d2d5a, 0x110f0f1e,
		0xcbb0b07b, 0xfc5454a8, 0xd6bbbb6d, 0x3a16162c ];

	var T2 = [
		0x6363c6a5, 0x7c7cf884, 0x7777ee99, 0x7b7bf68d,
		0xf2f2ff0d, 0x6b6bd6bd, 0x6f6fdeb1, 0xc5c59154,
		0x30306050, 0x01010203, 0x6767cea9, 0x2b2b567d,
		0xfefee719, 0xd7d7b562, 0xabab4de6, 0x7676ec9a,
		0xcaca8f45, 0x82821f9d, 0xc9c98940, 0x7d7dfa87,
		0xfafaef15, 0x5959b2eb, 0x47478ec9, 0xf0f0fb0b,
		0xadad41ec, 0xd4d4b367, 0xa2a25ffd, 0xafaf45ea,
		0x9c9c23bf, 0xa4a453f7, 0x7272e496, 0xc0c09b5b,
		0xb7b775c2, 0xfdfde11c, 0x93933dae, 0x26264c6a,
		0x36366c5a, 0x3f3f7e41, 0xf7f7f502, 0xcccc834f,
		0x3434685c, 0xa5a551f4, 0xe5e5d134, 0xf1f1f908,
		0x7171e293, 0xd8d8ab73, 0x31316253, 0x15152a3f,
		0x0404080c, 0xc7c79552, 0x23234665, 0xc3c39d5e,
		0x18183028, 0x969637a1, 0x05050a0f, 0x9a9a2fb5,
		0x07070e09, 0x12122436, 0x80801b9b, 0xe2e2df3d,
		0xebebcd26, 0x27274e69, 0xb2b27fcd, 0x7575ea9f,
		0x0909121b, 0x83831d9e, 0x2c2c5874, 0x1a1a342e,
		0x1b1b362d, 0x6e6edcb2, 0x5a5ab4ee, 0xa0a05bfb,
		0x5252a4f6, 0x3b3b764d, 0xd6d6b761, 0xb3b37dce,
		0x2929527b, 0xe3e3dd3e, 0x2f2f5e71, 0x84841397,
		0x5353a6f5, 0xd1d1b968, 0x00000000, 0xededc12c,
		0x20204060, 0xfcfce31f, 0xb1b179c8, 0x5b5bb6ed,
		0x6a6ad4be, 0xcbcb8d46, 0xbebe67d9, 0x3939724b,
		0x4a4a94de, 0x4c4c98d4, 0x5858b0e8, 0xcfcf854a,
		0xd0d0bb6b, 0xefefc52a, 0xaaaa4fe5, 0xfbfbed16,
		0x434386c5, 0x4d4d9ad7, 0x33336655, 0x85851194,
		0x45458acf, 0xf9f9e910, 0x02020406, 0x7f7ffe81,
		0x5050a0f0, 0x3c3c7844, 0x9f9f25ba, 0xa8a84be3,
		0x5151a2f3, 0xa3a35dfe, 0x404080c0, 0x8f8f058a,
		0x92923fad, 0x9d9d21bc, 0x38387048, 0xf5f5f104,
		0xbcbc63df, 0xb6b677c1, 0xdadaaf75, 0x21214263,
		0x10102030, 0xffffe51a, 0xf3f3fd0e, 0xd2d2bf6d,
		0xcdcd814c, 0x0c0c1814, 0x13132635, 0xececc32f,
		0x5f5fbee1, 0x979735a2, 0x444488cc, 0x17172e39,
		0xc4c49357, 0xa7a755f2, 0x7e7efc82, 0x3d3d7a47,
		0x6464c8ac, 0x5d5dbae7, 0x1919322b, 0x7373e695,
		0x6060c0a0, 0x81811998, 0x4f4f9ed1, 0xdcdca37f,
		0x22224466, 0x2a2a547e, 0x90903bab, 0x88880b83,
		0x46468cca, 0xeeeec729, 0xb8b86bd3, 0x1414283c,
		0xdedea779, 0x5e5ebce2, 0x0b0b161d, 0xdbdbad76,
		0xe0e0db3b, 0x32326456, 0x3a3a744e, 0x0a0a141e,
		0x494992db, 0x06060c0a, 0x2424486c, 0x5c5cb8e4,
		0xc2c29f5d, 0xd3d3bd6e, 0xacac43ef, 0x6262c4a6,
		0x919139a8, 0x959531a4, 0xe4e4d337, 0x7979f28b,
		0xe7e7d532, 0xc8c88b43, 0x37376e59, 0x6d6ddab7,
		0x8d8d018c, 0xd5d5b164, 0x4e4e9cd2, 0xa9a949e0,
		0x6c6cd8b4, 0x5656acfa, 0xf4f4f307, 0xeaeacf25,
		0x6565caaf, 0x7a7af48e, 0xaeae47e9, 0x08081018,
		0xbaba6fd5, 0x7878f088, 0x25254a6f, 0x2e2e5c72,
		0x1c1c3824, 0xa6a657f1, 0xb4b473c7, 0xc6c69751,
		0xe8e8cb23, 0xdddda17c, 0x7474e89c, 0x1f1f3e21,
		0x4b4b96dd, 0xbdbd61dc, 0x8b8b0d86, 0x8a8a0f85,
		0x7070e090, 0x3e3e7c42, 0xb5b571c4, 0x6666ccaa,
		0x484890d8, 0x03030605, 0xf6f6f701, 0x0e0e1c12,
		0x6161c2a3, 0x35356a5f, 0x5757aef9, 0xb9b969d0,
		0x86861791, 0xc1c19958, 0x1d1d3a27, 0x9e9e27b9,
		0xe1e1d938, 0xf8f8eb13, 0x98982bb3, 0x11112233,
		0x6969d2bb, 0xd9d9a970, 0x8e8e0789, 0x949433a7,
		0x9b9b2db6, 0x1e1e3c22, 0x87871592, 0xe9e9c920,
		0xcece8749, 0x5555aaff, 0x28285078, 0xdfdfa57a,
		0x8c8c038f, 0xa1a159f8, 0x89890980, 0x0d0d1a17,
		0xbfbf65da, 0xe6e6d731, 0x424284c6, 0x6868d0b8,
		0x414182c3, 0x999929b0, 0x2d2d5a77, 0x0f0f1e11,
		0xb0b07bcb, 0x5454a8fc, 0xbbbb6dd6, 0x16162c3a ];

	var T3 = [
		0x63c6a563, 0x7cf8847c, 0x77ee9977, 0x7bf68d7b,
		0xf2ff0df2, 0x6bd6bd6b, 0x6fdeb16f, 0xc59154c5,
		0x30605030, 0x01020301, 0x67cea967, 0x2b567d2b,
		0xfee719fe, 0xd7b562d7, 0xab4de6ab, 0x76ec9a76,
		0xca8f45ca, 0x821f9d82, 0xc98940c9, 0x7dfa877d,
		0xfaef15fa, 0x59b2eb59, 0x478ec947, 0xf0fb0bf0,
		0xad41ecad, 0xd4b367d4, 0xa25ffda2, 0xaf45eaaf,
		0x9c23bf9c, 0xa453f7a4, 0x72e49672, 0xc09b5bc0,
		0xb775c2b7, 0xfde11cfd, 0x933dae93, 0x264c6a26,
		0x366c5a36, 0x3f7e413f, 0xf7f502f7, 0xcc834fcc,
		0x34685c34, 0xa551f4a5, 0xe5d134e5, 0xf1f908f1,
		0x71e29371, 0xd8ab73d8, 0x31625331, 0x152a3f15,
		0x04080c04, 0xc79552c7, 0x23466523, 0xc39d5ec3,
		0x18302818, 0x9637a196, 0x050a0f05, 0x9a2fb59a,
		0x070e0907, 0x12243612, 0x801b9b80, 0xe2df3de2,
		0xebcd26eb, 0x274e6927, 0xb27fcdb2, 0x75ea9f75,
		0x09121b09, 0x831d9e83, 0x2c58742c, 0x1a342e1a,
		0x1b362d1b, 0x6edcb26e, 0x5ab4ee5a, 0xa05bfba0,
		0x52a4f652, 0x3b764d3b, 0xd6b761d6, 0xb37dceb3,
		0x29527b29, 0xe3dd3ee3, 0x2f5e712f, 0x84139784,
		0x53a6f553, 0xd1b968d1, 0x00000000, 0xedc12ced,
		0x20406020, 0xfce31ffc, 0xb179c8b1, 0x5bb6ed5b,
		0x6ad4be6a, 0xcb8d46cb, 0xbe67d9be, 0x39724b39,
		0x4a94de4a, 0x4c98d44c, 0x58b0e858, 0xcf854acf,
		0xd0bb6bd0, 0xefc52aef, 0xaa4fe5aa, 0xfbed16fb,
		0x4386c543, 0x4d9ad74d, 0x33665533, 0x85119485,
		0x458acf45, 0xf9e910f9, 0x02040602, 0x7ffe817f,
		0x50a0f050, 0x3c78443c, 0x9f25ba9f, 0xa84be3a8,
		0x51a2f351, 0xa35dfea3, 0x4080c040, 0x8f058a8f,
		0x923fad92, 0x9d21bc9d, 0x38704838, 0xf5f104f5,
		0xbc63dfbc, 0xb677c1b6, 0xdaaf75da, 0x21426321,
		0x10203010, 0xffe51aff, 0xf3fd0ef3, 0xd2bf6dd2,
		0xcd814ccd, 0x0c18140c, 0x13263513, 0xecc32fec,
		0x5fbee15f, 0x9735a297, 0x4488cc44, 0x172e3917,
		0xc49357c4, 0xa755f2a7, 0x7efc827e, 0x3d7a473d,
		0x64c8ac64, 0x5dbae75d, 0x19322b19, 0x73e69573,
		0x60c0a060, 0x81199881, 0x4f9ed14f, 0xdca37fdc,
		0x22446622, 0x2a547e2a, 0x903bab90, 0x880b8388,
		0x468cca46, 0xeec729ee, 0xb86bd3b8, 0x14283c14,
		0xdea779de, 0x5ebce25e, 0x0b161d0b, 0xdbad76db,
		0xe0db3be0, 0x32645632, 0x3a744e3a, 0x0a141e0a,
		0x4992db49, 0x060c0a06, 0x24486c24, 0x5cb8e45c,
		0xc29f5dc2, 0xd3bd6ed3, 0xac43efac, 0x62c4a662,
		0x9139a891, 0x9531a495, 0xe4d337e4, 0x79f28b79,
		0xe7d532e7, 0xc88b43c8, 0x376e5937, 0x6ddab76d,
		0x8d018c8d, 0xd5b164d5, 0x4e9cd24e, 0xa949e0a9,
		0x6cd8b46c, 0x56acfa56, 0xf4f307f4, 0xeacf25ea,
		0x65caaf65, 0x7af48e7a, 0xae47e9ae, 0x08101808,
		0xba6fd5ba, 0x78f08878, 0x254a6f25, 0x2e5c722e,
		0x1c38241c, 0xa657f1a6, 0xb473c7b4, 0xc69751c6,
		0xe8cb23e8, 0xdda17cdd, 0x74e89c74, 0x1f3e211f,
		0x4b96dd4b, 0xbd61dcbd, 0x8b0d868b, 0x8a0f858a,
		0x70e09070, 0x3e7c423e, 0xb571c4b5, 0x66ccaa66,
		0x4890d848, 0x03060503, 0xf6f701f6, 0x0e1c120e,
		0x61c2a361, 0x356a5f35, 0x57aef957, 0xb969d0b9,
		0x86179186, 0xc19958c1, 0x1d3a271d, 0x9e27b99e,
		0xe1d938e1, 0xf8eb13f8, 0x982bb398, 0x11223311,
		0x69d2bb69, 0xd9a970d9, 0x8e07898e, 0x9433a794,
		0x9b2db69b, 0x1e3c221e, 0x87159287, 0xe9c920e9,
		0xce8749ce, 0x55aaff55, 0x28507828, 0xdfa57adf,
		0x8c038f8c, 0xa159f8a1, 0x89098089, 0x0d1a170d,
		0xbf65dabf, 0xe6d731e6, 0x4284c642, 0x68d0b868,
		0x4182c341, 0x9929b099, 0x2d5a772d, 0x0f1e110f,
		0xb07bcbb0, 0x54a8fc54, 0xbb6dd6bb, 0x162c3a16 ];

	var T4 = [
		0xc6a56363, 0xf8847c7c, 0xee997777, 0xf68d7b7b,
		0xff0df2f2, 0xd6bd6b6b, 0xdeb16f6f, 0x9154c5c5,
		0x60503030, 0x02030101, 0xcea96767, 0x567d2b2b,
		0xe719fefe, 0xb562d7d7, 0x4de6abab, 0xec9a7676,
		0x8f45caca, 0x1f9d8282, 0x8940c9c9, 0xfa877d7d,
		0xef15fafa, 0xb2eb5959, 0x8ec94747, 0xfb0bf0f0,
		0x41ecadad, 0xb367d4d4, 0x5ffda2a2, 0x45eaafaf,
		0x23bf9c9c, 0x53f7a4a4, 0xe4967272, 0x9b5bc0c0,
		0x75c2b7b7, 0xe11cfdfd, 0x3dae9393, 0x4c6a2626,
		0x6c5a3636, 0x7e413f3f, 0xf502f7f7, 0x834fcccc,
		0x685c3434, 0x51f4a5a5, 0xd134e5e5, 0xf908f1f1,
		0xe2937171, 0xab73d8d8, 0x62533131, 0x2a3f1515,
		0x080c0404, 0x9552c7c7, 0x46652323, 0x9d5ec3c3,
		0x30281818, 0x37a19696, 0x0a0f0505, 0x2fb59a9a,
		0x0e090707, 0x24361212, 0x1b9b8080, 0xdf3de2e2,
		0xcd26ebeb, 0x4e692727, 0x7fcdb2b2, 0xea9f7575,
		0x121b0909, 0x1d9e8383, 0x58742c2c, 0x342e1a1a,
		0x362d1b1b, 0xdcb26e6e, 0xb4ee5a5a, 0x5bfba0a0,
		0xa4f65252, 0x764d3b3b, 0xb761d6d6, 0x7dceb3b3,
		0x527b2929, 0xdd3ee3e3, 0x5e712f2f, 0x13978484,
		0xa6f55353, 0xb968d1d1, 0x00000000, 0xc12ceded,
		0x40602020, 0xe31ffcfc, 0x79c8b1b1, 0xb6ed5b5b,
		0xd4be6a6a, 0x8d46cbcb, 0x67d9bebe, 0x724b3939,
		0x94de4a4a, 0x98d44c4c, 0xb0e85858, 0x854acfcf,
		0xbb6bd0d0, 0xc52aefef, 0x4fe5aaaa, 0xed16fbfb,
		0x86c54343, 0x9ad74d4d, 0x66553333, 0x11948585,
		0x8acf4545, 0xe910f9f9, 0x04060202, 0xfe817f7f,
		0xa0f05050, 0x78443c3c, 0x25ba9f9f, 0x4be3a8a8,
		0xa2f35151, 0x5dfea3a3, 0x80c04040, 0x058a8f8f,
		0x3fad9292, 0x21bc9d9d, 0x70483838, 0xf104f5f5,
		0x63dfbcbc, 0x77c1b6b6, 0xaf75dada, 0x42632121,
		0x20301010, 0xe51affff, 0xfd0ef3f3, 0xbf6dd2d2,
		0x814ccdcd, 0x18140c0c, 0x26351313, 0xc32fecec,
		0xbee15f5f, 0x35a29797, 0x88cc4444, 0x2e391717,
		0x9357c4c4, 0x55f2a7a7, 0xfc827e7e, 0x7a473d3d,
		0xc8ac6464, 0xbae75d5d, 0x322b1919, 0xe6957373,
		0xc0a06060, 0x19988181, 0x9ed14f4f, 0xa37fdcdc,
		0x44662222, 0x547e2a2a, 0x3bab9090, 0x0b838888,
		0x8cca4646, 0xc729eeee, 0x6bd3b8b8, 0x283c1414,
		0xa779dede, 0xbce25e5e, 0x161d0b0b, 0xad76dbdb,
		0xdb3be0e0, 0x64563232, 0x744e3a3a, 0x141e0a0a,
		0x92db4949, 0x0c0a0606, 0x486c2424, 0xb8e45c5c,
		0x9f5dc2c2, 0xbd6ed3d3, 0x43efacac, 0xc4a66262,
		0x39a89191, 0x31a49595, 0xd337e4e4, 0xf28b7979,
		0xd532e7e7, 0x8b43c8c8, 0x6e593737, 0xdab76d6d,
		0x018c8d8d, 0xb164d5d5, 0x9cd24e4e, 0x49e0a9a9,
		0xd8b46c6c, 0xacfa5656, 0xf307f4f4, 0xcf25eaea,
		0xcaaf6565, 0xf48e7a7a, 0x47e9aeae, 0x10180808,
		0x6fd5baba, 0xf0887878, 0x4a6f2525, 0x5c722e2e,
		0x38241c1c, 0x57f1a6a6, 0x73c7b4b4, 0x9751c6c6,
		0xcb23e8e8, 0xa17cdddd, 0xe89c7474, 0x3e211f1f,
		0x96dd4b4b, 0x61dcbdbd, 0x0d868b8b, 0x0f858a8a,
		0xe0907070, 0x7c423e3e, 0x71c4b5b5, 0xccaa6666,
		0x90d84848, 0x06050303, 0xf701f6f6, 0x1c120e0e,
		0xc2a36161, 0x6a5f3535, 0xaef95757, 0x69d0b9b9,
		0x17918686, 0x9958c1c1, 0x3a271d1d, 0x27b99e9e,
		0xd938e1e1, 0xeb13f8f8, 0x2bb39898, 0x22331111,
		0xd2bb6969, 0xa970d9d9, 0x07898e8e, 0x33a79494,
		0x2db69b9b, 0x3c221e1e, 0x15928787, 0xc920e9e9,
		0x8749cece, 0xaaff5555, 0x50782828, 0xa57adfdf,
		0x038f8c8c, 0x59f8a1a1, 0x09808989, 0x1a170d0d,
		0x65dabfbf, 0xd731e6e6, 0x84c64242, 0xd0b86868,
		0x82c34141, 0x29b09999, 0x5a772d2d, 0x1e110f0f,
		0x7bcbb0b0, 0xa8fc5454, 0x6dd6bbbb, 0x2c3a1616 ];

	function B0(x) { return (x&255); }
	function B1(x) { return ((x>>8)&255); }
	function B2(x) { return ((x>>16)&255); }
	function B3(x) { return ((x>>24)&255); }

	function F1(x0, x1, x2, x3)
	{
		return B1(T1[x0&255]) | (B1(T1[(x1>>8)&255])<<8)
			| (B1(T1[(x2>>16)&255])<<16) | (B1(T1[x3>>>24])<<24);
	}

	function packBytes(octets)
	{
		var i, j;
		var len=octets.length;
		var b=new Array(len/4);

		if (!octets || len % 4) return;

		for (i=0, j=0; j<len; j+= 4)
			b[i++] = octets[j] | (octets[j+1]<<8) | (octets[j+2]<<16) | (octets[j+3]<<24);

		return b;  
	}

	function unpackBytes(packed)
	{
		var j;
		var i=0, l = packed.length;
		var r = new Array(l*4);

		for (j=0; j<l; j++)
		{
			r[i++] = B0(packed[j]);
			r[i++] = B1(packed[j]);
			r[i++] = B2(packed[j]);
			r[i++] = B3(packed[j]);
		}
		return r;
	}

	// ------------------------------------------------

	var maxkc=8;
	var maxrk=14;

	function keyExpansion(key)
	{
		var kc, i, j, r, t;
		var rounds;
		var keySched=new Array(maxrk+1);
		var keylen=key.length;
		var k=new Array(maxkc);
		var tk=new Array(maxkc);
		var rconpointer=0;

		if(keylen==16)
		{
			rounds=10;
			kc=4;
		}
		else if(keylen==24)
		{
			rounds=12;
			kc=6
		}
		else if(keylen==32)
		{
			rounds=14;
			kc=8
		}
		else
		{
			fail('Invalid key length '+keylen);
			return;
		}

		for(i=0; i<maxrk+1; i++) keySched[i]=new Array(4);

		for(i=0,j=0; j<keylen; j++,i+=4)
			k[j] = key.charCodeAt(i) | (key.charCodeAt(i+1)<<8)
            | (key.charCodeAt(i+2)<<16) | (key.charCodeAt(i+3)<<24);

		for(j=kc-1; j>=0; j--) tk[j] = k[j];

		r=0;
		t=0;
		for(j=0; (j<kc)&&(r<rounds+1); )
		{
			for(; (j<kc)&&(t<4); j++,t++)
			{
				keySched[r][t]=tk[j];
			}
			if(t==4)
			{
				r++;
				t=0;
			}
		}

		while(r<rounds+1)
		{
			var temp = tk[kc-1];

			tk[0] ^= S[B1(temp)] | (S[B2(temp)]<<8) | (S[B3(temp)]<<16) | (S[B0(temp)]<<24);
			tk[0] ^= Rcon[rconpointer++];

			if(kc != 8)
			{
				for(j=1; j<kc; j++) tk[j] ^= tk[j-1];
			}
			else
			{
				for(j=1; j<kc/2; j++) tk[j] ^= tk[j-1];
				
				temp = tk[kc/2-1];
				tk[kc/2] ^= S[B0(temp)] | (S[B1(temp)]<<8) | (S[B2(temp)]<<16) | (S[B3(temp)]<<24);

				for(j=kc/2+1; j<kc; j++) tk[j] ^= tk[j-1];
			}

			for(j=0; (j<kc)&&(r<rounds+1); )
			{
				for(; (j<kc)&&(t<4); j++,t++)
				{
					keySched[r][t]=tk[j];
				}
				if(t==4)
				{
					r++;
					t=0;
				}
			}
		}
		this.rounds = rounds;
		this.rk = keySched;
		return this;
	}

	function AESencrypt(block, ctx)
	{
		var r;
		var t0,t1,t2,t3;

		var b = packBytes(block);
		var rounds = ctx.rounds;
		var b0 = b[0];
		var b1 = b[1];
		var b2 = b[2];
		var b3 = b[3];

		for(r=0; r<rounds-1; r++)
		{
			t0 = b0 ^ ctx.rk[r][0];
			t1 = b1 ^ ctx.rk[r][1];
			t2 = b2 ^ ctx.rk[r][2];
			t3 = b3 ^ ctx.rk[r][3];

			b0 = T1[t0&255] ^ T2[(t1>>8)&255] ^ T3[(t2>>16)&255] ^ T4[t3>>>24];
			b1 = T1[t1&255] ^ T2[(t2>>8)&255] ^ T3[(t3>>16)&255] ^ T4[t0>>>24];
			b2 = T1[t2&255] ^ T2[(t3>>8)&255] ^ T3[(t0>>16)&255] ^ T4[t1>>>24];
			b3 = T1[t3&255] ^ T2[(t0>>8)&255] ^ T3[(t1>>16)&255] ^ T4[t2>>>24];
		}

		// last round is special
		r = rounds-1;

		t0 = b0 ^ ctx.rk[r][0];
		t1 = b1 ^ ctx.rk[r][1];
		t2 = b2 ^ ctx.rk[r][2];
		t3 = b3 ^ ctx.rk[r][3];

		b[0] = F1(t0, t1, t2, t3) ^ ctx.rk[rounds][0];
		b[1] = F1(t1, t2, t3, t0) ^ ctx.rk[rounds][1];
		b[2] = F1(t2, t3, t0, t1) ^ ctx.rk[rounds][2];
		b[3] = F1(t3, t0, t1, t2) ^ ctx.rk[rounds][3];

		return unpackBytes(b);
	}

	/*************** http://www.hanewin.net/encrypt/base64.js *******************/

	/* OpenPGP radix-64/base64 string encoding/decoding
	 * Copyright 2005 Herbert Hanewinkel, www.haneWIN.de
	 * version 1.0, check www.haneWIN.de for the latest version

	 * This software is provided as-is, without express or implied warranty.  
	 * Permission to use, copy, modify, distribute or sell this software, with or
	 * without fee, for any purpose and by any individual or organization, is hereby
	 * granted, provided that the above copyright notice and this paragraph appear 
	 * in all copies. Distribution as a part of an application or binary must
	 * include the above copyright notice in the documentation and/or other materials
	 * provided with the application or distribution.
	 */

	var b64s='ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'

	function s2r(t)
	{
		var a, c, n;
		var r='', l=0, s=0;
		var tl=t.length;

		for(n=0; n<tl; n++)
		{
			c=t.charCodeAt(n);
			if(s == 0)
			{
				r+=b64s.charAt((c>>2)&63);
				a=(c&3)<<4;
			}
			else if(s==1)
			{
				r+=b64s.charAt((a|(c>>4)&15));
				a=(c&15)<<2;
			}
			else if(s==2)
			{
				r+=b64s.charAt(a|((c>>6)&3));
				l+=1;
				if((l%60)==0) r+="\n";
				r+=b64s.charAt(c&63);
			}
			l+=1;
			if((l%60)==0) r+="\n";

			s+=1;
			if(s==3) s=0;  
		}
		if(s>0)
		{
			r+=b64s.charAt(a);
			l+=1;
			if((l%60)==0) r+="\n";
			r+='=';
			l+=1;
		}
		if(s==1)
		{
			if((l%60)==0) r+="\n";
			r+='=';
		}

		return r;
	}

	function r2s(t)
	{
		var c, n;
		var r='', s=0, a=0;
		var tl=t.length;

		for(n=0; n<tl; n++)
		{
			c=b64s.indexOf(t.charAt(n));
			if(c >= 0)
			{
				if(s) r+=String.fromCharCode(a | (c>>(6-s))&255);
				s=(s+2)&7;
				a=(c<<s)&255;
			}
		}
		return r;
	}

	/*************** http://www.hanewin.net/encrypt/mouse.js *******************/
    
	/* Collect entropy from mouse motion and key press events
	 * Note that this is coded to work with either DOM2 or Internet Explorer
	 * style events.
	 * We don't use every successive mouse movement event.
	 * Instead, we use some bits from random() to determine how many
	 * subsequent mouse movements we ignore before capturing the next one.
	 * rc4 is used as a mixing function for the captured mouse events.  
	 *
	 * mouse motion event code originally from John Walker
	 * key press timing code thanks to Nigel Johnstone
	 */

	var oldKeyHandler;    // For saving and restoring key press handler in IE4
	var keyRead = 0;
	var keyNext = 0;
	var keyArray = new Array(256);
	
	var mouseMoveSkip = 0; // Delay counter for mouse entropy collection
	var oldMoveHandler;    // For saving and restoring mouse move handler in IE4
	var mouseRead = 0;
	var mouseNext = 0;
	var mouseArray = new Array(256);

	// ----------------------------------------

	var s=new Array(256);
	var x, y;

	function rc4Init()
	{
		var i, t;
		var key = new Array(256);

		for(i=0; i<256; i++)
		{
			s[i]=i;
			key[i] = randomByte()^timeByte();
		}

		y=0;
		for(i=0; i<2; i++)
		{
			for(x=0; x<256; x++)
			{
				y=(key[i] + s[x] + y) % 256;
				t=s[x]; s[x]=s[y]; s[y]=t;
			}
		}
		x=0;
		y=0;
	}

	function rc4Next(b)
	{
		var t, x2;

		x=(x+1) & 255; 
		y=(s[x] + y) & 255;
		t=s[x]; s[x]=s[y]; s[y]=t;
		return (b ^ s[(s[x] + s[y]) % 256]) & 255; 
	}

	// ----------------------------------------
    
	function keyByte() { return keyArray[(keyRead++)%keyNext]; }
	function keyPressEntropy(e) { keyArray[(keyNext++)%256] ^= timeByte(); }

	function mouseByte() { return mouseArray[(mouseRead++)%mouseNext]; }
	function mouseMoveEntropy(e)
	{
		var c;

		if (!e) { e = window.event; }    // Internet Explorer event model

		if(mouseMoveSkip-- <= 0)
		{
			if(oldMoveHandler) { c = ((e.clientX << 4) | (e.clientY & 15)); }
			else { c = ((e.screenX << 4) | (e.screenY & 15)); }

			mouseArray[(mouseNext++)%256] ^= rc4Next(c&255);
			mouseArray[(mouseNext++)%256] ^= rc4Next(timeByte());
			mouseMoveSkip = randomByte() & 7;
		}
	}

	// ----------------------------------------

	function eventsEnd()
	{
		if(document.removeEventListener)
		{
			document.removeEventListener("mousemove", mouseMoveEntropy, false);
			document.removeEventListener("keypress", keyPressEntropy, false);
		}
		else if(document.detachEvent)
		{
			document.detachEvent("onmousemove", mouseMoveEntropy);
			document.detachEvent("onkeypress", keyPressEntropy);
		}
		else if(document.releaseEvents)
		{
			document.releaseEvents(EVENT.MOUSEMOVE); document.onMousemove = 0;
			document.releaseEvents(EVENT.KEYPRESS); document.onKeypress = 0;
		}
		else
		{
			document.onMousemove = oldMoveHandler;
			document.onKeypress = oldKeyHandler;
		}
	}

	// Start collection of entropy.
	
	function eventsCollect()
	{
		if((document.implementation.hasFeature("Events", "2.0"))
		   && document.addEventListener) // Document Object Model (DOM) 2 events
		{
			document.addEventListener("mousemove", mouseMoveEntropy, false);
			document.addEventListener("keypress", keyPressEntropy, false);
		}
		else if(document.attachEvent) // IE 5 and above event model
		{
			document.attachEvent("onmousemove", mouseMoveEntropy);
			document.attachEvent("onkeypress", keyPressEntropy);
		}
		else if(document.captureEvents) // Netscape 4.0
		{
			document.captureEvents(Event.MOUSEMOVE);
			document.onMousemove = mouseMoveEntropy;
			document.captureEvents(Event.KEYPRESS);
			document.onMousemove = keyPressEntropy;
		}
		else // IE 4 event model
		{
			oldMoveHandler = document.onmousemove;
			document.onMousemove = mouseMoveEntropy;
			oldKeyHandler = document.onkeypress;
			document.onKeypress = keyPressEntropy;
		}

		rc4Init();
	}

	/*************** http://www.hanewin.net/encrypt/PGencode.js *******************/

	/* OpenPGP encryption using RSA/AES
	 * Copyright 2005-2006 Herbert Hanewinkel, www.haneWIN.de
	 * version 2.0, check www.haneWIN.de for the latest version

	 * This software is provided as-is, without express or implied warranty.  
	 * Permission to use, copy, modify, distribute or sell this software, with or
	 * without fee, for any purpose and by any individual or organization, is hereby
	 * granted, provided that the above copyright notice and this paragraph appear 
	 * in all copies. Distribution as a part of an application or binary must
	 * include the above copyright notice in the documentation and/or other
	 * materials provided with the application or distribution.
	 */

	/* We need an unpredictable session key of 128 bits ( = 2^128 possible keys).
	 * If we generate the session key with a PRNG from a small seed we get only
	 * a small number of session keys, e.g. 4 bytes seed => 2^32 keys, a brute
	 * force attack could try all 2^32 session keys. 
	 * (see RFC 1750 - Randomness Recommendations for Security.)
	 *
	 * Sources for randomness in Javascript are limited.
	 * We have load, exec time, seed from random(), mouse movement events
	 * and the timing from key press events.
	 * But even here we have restrictions.
	 * - A mailer will add a timestamp to the encrypted message, therefore
	 *   only the msecs from the clock can be seen as unpredictable.
	 * - Because the Windows timer is still based on the old DOS timer,
	 *   the msecs jump under Windows in 18.2 msecs steps.
	 * - Only a few bits from mouse mouvement event coordinates are unpredictable,
	 *   if the same buttons are clicked on the screen.
	 */

	var rnArray = new Array(256);
	var rnNext = 0;
	var rnRead = 0;

	function randomByte() { return Math.round(Math.random()*255)&255; }
	function timeByte() { return ((new Date().getTime())>>>2)&255; }

	rnTimer = function()
	{
		var t = timeByte(); // load time

		for(var i=0; i<256; i++)
		{
			t ^= randomByte();
			rnArray[(rnNext++)&255] ^= t;
		} 
		window.setTimeout("rnTimer()",randomByte()|128);
	}

	// rnTimer() and mouseMoveCollect() are started on page load.

	rnTimer();
	eventsCollect();

	// ----------------------------------------

	function randomString(len, nozero)
	{
		var r = '';
		var t = timeByte(); // exec time

		for(var i=0; i<len;)
		{
			t ^= rnArray[(rnRead++)&255]^mouseByte()^keyByte();
			if(t==0 && nozero) continue;
			i++;

			r+=String.fromCharCode(t);
		}
		return r;
	}

	// ----------------------------------------

	function hex2s(hex)
	{
		var r='';
		if(hex.length%2) hex+='0';

		for(var i = 0; i<hex.length; i += 2)
			r += String.fromCharCode(parseInt(hex.slice(i, i+2), 16));
		return r;
	}

	function crc24(data)
	{
		var crc = 0xb704ce;

		for(var n=0; n<data.length;n++)
		{
			crc ^=(data.charCodeAt(n)&255)<<16;
			for(i=0;i<8;i++)
			{
				crc<<=1;
				if(crc & 0x1000000) crc^=0x1864cfb;
			}       
		}
		return String.fromCharCode((crc>>16)&255)
			+String.fromCharCode((crc>>8)&255)
			+String.fromCharCode(crc&255);
	}

	// --------------------------------------
	// GPG CFB symmetric encryption using AES

	var symAlg = 7;          // AES=7, AES192=8, AES256=9
	var kSize  = [16,24,32]  // key length in bytes
	var bpbl   = 16;         // bytes per data block

	function GPGencrypt(key, text)
	{
		var i, n;
		var len = text.length;
		var lsk = key.length;
		var iblock = new Array(bpbl)
		var rblock = new Array(bpbl);
		var ct = new Array(bpbl+2);
		var expandedKey = new Array();
		
		var ciphertext = '';

		// append zero padding
		if(len%bpbl)
		{
			for(i=(len%bpbl); i<bpbl; i++) text+='\0';
		}
		
		expandedKey = keyExpansion(key);

		// set up initialisation vector and random byte vector
		for(i=0; i<bpbl; i++)
		{
			iblock[i] = 0;
			rblock[i] = randomByte();
		}

		iblock = AESencrypt(iblock, expandedKey);
		for(i=0; i<bpbl; i++)
		{
			ct[i] = (iblock[i] ^= rblock[i]);
		}

		iblock = AESencrypt(iblock, expandedKey);
		// append check octets
		ct[bpbl]   = (iblock[0] ^ rblock[bpbl-2]);
		ct[bpbl+1] = (iblock[1] ^ rblock[bpbl-1]);
		
		for(i = 0; i < bpbl+2; i++) ciphertext += String.fromCharCode(ct[i]);

		// resync
		iblock = ct.slice(2, bpbl+2);

		for(n = 0; n < text.length; n+=bpbl)
		{
			iblock = AESencrypt(iblock, expandedKey);
			for(i = 0; i < bpbl; i++)
			{
				iblock[i] ^= text.charCodeAt(n+i);
				ciphertext += String.fromCharCode(iblock[i]);
			}
		}
		return ciphertext.substr(0,len+bpbl+2);
	}

	// ------------------------------
	// GPG packet header (old format)

	function GPGpkt(tag, len)
	{
		if(len>255) tag +=1;
		var h = String.fromCharCode(tag);
		if(len>255) h+=String.fromCharCode(len/256);
		h += String.fromCharCode(len%256);
		return h;
	}

	// ----------------------------------------------
	// GPG public key encryted session key packet (1)

	var el = [3,5,9,17,513,2049,4097,8193];

	function GPGpkesk(keyId, keytyp, symAlgo, sessionkey, pkey)
	{ 
		var mod=new Array();
		var exp=new Array();
		var enc='';
		
		var s = r2s(pkey);
		var l = Math.floor((s.charCodeAt(0)*256 + s.charCodeAt(1)+7)/8);

		mod = mpi2b(s.substr(0,l+2));

		if(keytyp)
		{
			var grp=new Array();
			var y  =new Array();
			var B  =new Array();
			var C  =new Array();

			var l2 = Math.floor((s.charCodeAt(l+2)*256 + s.charCodeAt(l+3)+7)/8)+2;

			grp = mpi2b(s.substr(l+2,l2));
			y   = mpi2b(s.substr(l+2+l2));
			exp[0] = 9; //el[randomByte()&7];
			B = bmodexp(grp,exp,mod);
			C = bmodexp(y,exp,mod);
		}
		else
		{
			exp = mpi2b(s.substr(l+2));
		}

		var lsk = sessionkey.length;

		// calculate checksum of session key
		var c = 0;
		for(var i = 0; i < lsk; i++) c += sessionkey.charCodeAt(i);
		c &= 0xffff;

		// create MPI from session key using PKCS-1 block type 02
		var lm = (l-2)*8+2;
		var m = String.fromCharCode(lm/256)+String.fromCharCode(lm%256)
			+String.fromCharCode(2)         // skip leading 0 for MPI
			+randomString(l-lsk-6,1)+'\0'   // add random padding (non-zero)
			+String.fromCharCode(symAlgo)+sessionkey
			+String.fromCharCode(c/256)+String.fromCharCode(c&255);

		if(keytyp)
		{
			// add Elgamal encrypted mpi values
			enc = b2mpi(B)+b2mpi(bmod(bmul(mpi2b(m),C),mod));

			return GPGpkt(0x84,enc.length+10)
				+String.fromCharCode(3)+keyId+String.fromCharCode(16)+enc;
		}
		else
		{
			// rsa encrypt the result and convert into mpi
			enc = b2mpi(bmodexp(mpi2b(m),exp,mod));

			return GPGpkt(0x84,enc.length+10)
				+String.fromCharCode(3)+keyId+String.fromCharCode(1)+enc;
		}
	}

	// ------------------------------------------
	// GPG literal data packet (11) for text file

	function GPGld(text)
	{
		if(text.indexOf('\r\n') == -1)
			text = text.replace(/\n/g,'\r\n');
		return GPGpkt(0xAC,text.length+10)+'t'
			+String.fromCharCode(4)+'file\0\0\0\0'+text;
	}

	// -------------------------------------------
	// GPG symmetrically encrypted data packet (9)

	function GPGsed(key, text)
	{
		var enc = GPGencrypt(key, GPGld(text));
		return GPGpkt(0xA4,enc.length)+enc;
	}

	// ------------------------------------------------

	function doEncrypt(keyId,publicKeyTypeValue,pkey,text)
	{
		var keytyp;
		if(publicKeyTypeValue === 'RSA') {
			keytyp = 0;
		} else if(publicKeyTypeValue === 'Elgamal') {
			keytyp = 1;
		} else {
			fail("Unknown key type: " + publicKeyTypeValue);
		}
		var keylen = kSize[symAlg-7];  // session key length in bytes

		var sesskey = randomString(keylen,0);
		keyId = hex2s(keyId);
		var cp = GPGpkesk(keyId,keytyp,symAlg,sesskey,pkey)+GPGsed(sesskey,text);

		return '-----BEGIN PGP MESSAGE-----\nVersion: haneWIN JavascriptPG v2.0\n\n'
			+s2r(cp)+'\n='+s2r(crc24(cp))+'\n-----END PGP MESSAGE-----\n';
	}

	/*************** http://www.hanewin.net/encrypt/PGencode.htm *******************/

	var defaultPublicKeyType = 'RSA',      // 0=RSA, 1=Elgamal
	defaultPublicKeyId = '02044b001cd7a551',
	defaultPublicKey = 'BADelitpUqMZLn+bryZR5rK9J3eu+pRVFP5tpboOlIwO2vqO/rCi8VvT2TPzEJarWhyZ465NIohYCiia9vaGUEp4rsDzFnVNgpON47yPew1zCmOOofituf+X6Qlaxylm5NnO4vnRcmoF4IbGwSCqyGgGor29D75Hovwlj1q6BWHYWwAGKQ==';

	// function load()
	// {
	// 	document.t.pkey.value=pubkey;
	// 	document.t.keyid.value=keyid;
	// 	if(keytyp == 0) document.t.pktype.value='RSA';
	// 	if(keytyp == 1) document.t.pktype.value='ELGAMAL';
	// }

	// function encrypt()
	// {
	// 	pubkey=document.t.pkey.value;

	// 	if(document.t.keyid.value.length) keyid=document.t.keyid.value;
	// 	else                              keyid='0000000000000000';
	// 	if(keyid.length != 16)
	// 	{
	// 		alert('Invalid Key Id');
	// 		return;
	// 	} 
		
	// 	keytyp = -1;
	// 	if(document.t.pktype.value == 'ELGAMAL') keytyp = 1;
	// 	if(document.t.pktype.value == 'RSA')     keytyp = 0;
	// 	if(keytyp == -1)
	// 	{
	// 		alert('Unsupported Key Type');
	// 		return;
	// 	} 

	// 	var startTime=new Date();

	// 	var text=document.t.text.value+'\r\n';
	// 	document.t.text.value=doEncrypt(keyid, keytyp, pubkey, text);

	// 	var endTime=new Date();
	// 	document.t.howLong.value=(endTime.getTime()-startTime.getTime())/1000.0;
	// }

	/* Gmail GPG 
	 *
	 *
	 */

	//
	// Constant Definitions
	//
	var containerId = 'gmail-gpg',
	publicKeyId = containerId + '-public-key',
	publicKeyTypeId = containerId + '-public-key-type',
	publicKeyIdId = containerId + '-public-key-id',
	publicKeyTypes = [ 'RSA', 'Elgamal' ],

	//
	// Find stuff on the page
	// 

	// Obtain reference to content of big Gmail frame, which is our document.
	iframe = document.getElementById('canvas_frame'),
	gmailDoc = iframe.contentDocument || iframe.contentWindow.document,
	
	//
	// Function definitions
	// 

	/**
	  * Alert the user about a failure, throw us out of the bookmarklet.
	  */
	fail = function ( msg ) {
		alert( msg );
		throw( msg );
	},

	/**
      * Encrypt the body of your gmail message.
      */
	encrypt = function () {

		//var privateKeyValue = prompt("Enter your private key, please!"),
		publicKeyValue = gmailDoc.getElementById( publicKeyId ).value,
		publicKeyTypeValue = gmailDoc.getElementById( publicKeyTypeId ).value,
		publicKeyIdValue = gmailDoc.getElementById( publicKeyIdId ).value,
		bodyTextarea = gmailDoc.getElementsByName('body')[0];// Find the body textarea

		// if( privateKeyValue === '' ) {
		// 	fail( "You must enter a private key." );
		// }
		if( publicKeyValue === '' ) {
			fail( "You must enter a public key." );
		}
		
		if( publicKeyIdValue === '' ) {
			//fail( "You must enter a public key ID." );
			publicKeyIdValue = '0000000000000000';
		} else if( publicKeyIdValue.length !== 16 ) {
			fail( "Your public key ID must be 16 characters long." );
		}
		
		// var startTime=new Date();

		// var text=document.t.text.value+'\r\n';
		var encrypted = doEncrypt(publicKeyIdValue, publicKeyTypeValue, publicKeyValue, bodyTextarea.value + '\r\n');
		bodyTextarea.value = encrypted;
		// var endTime=new Date();
		// document.t.howLong.value=(endTime.getTime()-startTime.getTime())/1000.0;
	},

	/**
      * Add an `encrypt' button.
      */
	buildInterface = function() {
		var divElements = gmailDoc.getElementsByTagName('div'),
		discardButton = null;
		
		// Find the div with text 'Discard'.
		for( var i = 0 ; i < divElements.length ; i ++ ) {
			// Is a text node.
			var div = divElements[i];
			if( div.firstChild !== null ) { // is this the best way to detect absence of child?
				var child = div.firstChild;
				if( child.nodeType === 3 ) {
					if( child.nodeValue === 'Discard' ) {
						discardButton = div;
						// we've found our discard button, break out of loop.
						break;
					}
				}
			}
		}

		// Fail out if we don't know where to put button.
		if( discardButton === null ) {
			fail( "Could not find Gmail's `Discard' button" );
		}

		// Find an appropriate text class for labels.
		var textClass = discardButton.parentNode.getElementsByTagName('span')[0].className,

		// Generate the interface elements
		containerDiv = gmailDoc.createElement( 'div' ),
		encryptButton = gmailDoc.createElement( 'div' ),
		publicKeyLabel = gmailDoc.createElement( 'label' ),
		publicKeyInput = gmailDoc.createElement( 'textarea' ),
		publicKeyTypeLabel = gmailDoc.createElement( 'label' ),
		publicKeyTypeSelect = gmailDoc.createElement( 'select' ),
		publicKeyIdLabel = gmailDoc.createElement( 'label' ),
		publicKeyIdInput = gmailDoc.createElement( 'textarea' );
		
		// Set up container div
		containerDiv.id = containerId;
		
		// Set up encrypt button
		encryptButton.setAttribute('role', 'button'); // necessary?
		encryptButton.className = discardButton.className; // copy styling
		encryptButton.appendChild( gmailDoc.createTextNode( 'Encrypt' )); // set text
		encryptButton.onclick = encrypt; // call 'encrypt' on click

		// Set up public key label
		publicKeyLabel.appendChild( gmailDoc.createTextNode( 'Public Key:' )); // set label text
		publicKeyLabel.htmlFor = publicKeyId; // set 'for' property
		publicKeyLabel.className = textClass;

		// Set up public key input
		publicKeyInput.id = publicKeyId;
		publicKeyInput.name = publicKeyId;
		publicKeyInput.value = defaultPublicKey; // TODO default?
		publicKeyInput.setAttribute('spellcheck', 'false');

		// Set up public key type label
		publicKeyTypeLabel.appendChild( gmailDoc.createTextNode( 'Public Key Type:' )); // set label text
		publicKeyTypeLabel.htmlFor = publicKeyTypeId; // set 'for' property
		publicKeyTypeLabel.className = textClass;

		// Set up public key type selector
		publicKeyTypeSelect.id = publicKeyTypeId;
		publicKeyTypeSelect.name = publicKeyTypeId;
		for( var i = 0 ; i < publicKeyTypes.length ; i ++ ) {
			var publicKeyType = publicKeyTypes[i],
			publicKeyTypeOption = gmailDoc.createElement( 'option' ); // create the option
			publicKeyTypeOption.appendChild( gmailDoc.createTextNode( publicKeyType )); // set text
			publicKeyTypeSelect.appendChild( publicKeyTypeOption ); // append to select
		}

		// Set up public key ID label
		publicKeyIdLabel.appendChild( gmailDoc.createTextNode( 'Public Key ID:' )); // set label text
		publicKeyIdLabel.htmlFor = publicKeyIdId;
		publicKeyIdLabel.className = textClass;
		
		// Set up public key ID input
		publicKeyIdInput.id = publicKeyIdId;
		publicKeyIdInput.name = publicKeyIdId;
		publicKeyIdInput.value = defaultPublicKeyId; // TODO default?
		publicKeyIdInput.setAttribute('spellcheck', 'false');

		// Lay it on down brother
		containerDiv.appendChild( encryptButton );
		containerDiv.appendChild( publicKeyLabel );
		containerDiv.appendChild( publicKeyInput );
		containerDiv.appendChild( publicKeyTypeLabel );
		containerDiv.appendChild( publicKeyTypeSelect );
		containerDiv.appendChild( publicKeyIdLabel );
		containerDiv.appendChild( publicKeyIdInput );

		discardButton.parentNode.insertBefore( containerDiv ); // insert before the discard button
	};
	
	// 
	// Function executions 
	//

	// Remove the existing interface if it already exists
	if( gmailDoc.getElementById( containerId ) !== null ) {
		var containerDiv = gmailDoc.getElementById( containerId );
		containerDiv.parentNode.removeChild( containerDiv );
	}
	buildInterface();
})();
