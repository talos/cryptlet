/**
  * Cryptlet :: A little bit 'o' privacy for Gmail in a bookmarklet.
  *
  * Uses the Stanford Javascript Crypto Library
  *
  * http://crypto.stanford.edu/sjcl/
  *
  * Default encryption generates a 128-bit symmetric AES key with
  * randomized salts and initialization vectors, and encrypts using
  * CCM mode.
  *
  * Copyright John Krauss 2011
  * Licensed under the BSD license.  See BSD.license for details.
  */

(function () {

    /*************** http://crypto.stanford.edu/sjcl/sjcl.js *******************/
"use strict";var sjcl={cipher:{},hash:{},keyexchange:{},mode:{},misc:{},codec:{},exception:{corrupt:function(a){this.toString=function(){return"CORRUPT: "+this.message};this.message=a},invalid:function(a){this.toString=function(){return"INVALID: "+this.message};this.message=a},bug:function(a){this.toString=function(){return"BUG: "+this.message};this.message=a},notReady:function(a){this.toString=function(){return"NOT READY: "+this.message};this.message=a}}};
sjcl.cipher.aes=function(a){this.h[0][0][0]||this.u();var b,c,d,e,f=this.h[0][4],g=this.h[1];b=a.length;var h=1;if(b!==4&&b!==6&&b!==8)throw new sjcl.exception.invalid("invalid aes key size");this.a=[d=a.slice(0),e=[]];for(a=b;a<4*b+28;a++){c=d[a-1];if(a%b===0||b===8&&a%b===4){c=f[c>>>24]<<24^f[c>>16&255]<<16^f[c>>8&255]<<8^f[c&255];if(a%b===0){c=c<<8^c>>>24^h<<24;h=h<<1^(h>>7)*283}}d[a]=d[a-b]^c}for(b=0;a;b++,a--){c=d[b&3?a:a-4];e[b]=a<=4||b<4?c:g[0][f[c>>>24]]^g[1][f[c>>16&255]]^g[2][f[c>>8&255]]^
g[3][f[c&255]]}};
sjcl.cipher.aes.prototype={encrypt:function(a){return this.F(a,0)},decrypt:function(a){return this.F(a,1)},h:[[[],[],[],[],[]],[[],[],[],[],[]]],u:function(){var a=this.h[0],b=this.h[1],c=a[4],d=b[4],e,f,g,h=[],i=[],k,j,l,m;for(e=0;e<0x100;e++)i[(h[e]=e<<1^(e>>7)*283)^e]=e;for(f=g=0;!c[f];f^=k||1,g=i[g]||1){l=g^g<<1^g<<2^g<<3^g<<4;l=l>>8^l&255^99;c[f]=l;d[l]=f;j=h[e=h[k=h[f]]];m=j*0x1010101^e*0x10001^k*0x101^f*0x1010100;j=h[l]*0x101^l*0x1010100;for(e=0;e<4;e++){a[e][f]=j=j<<24^j>>>8;b[e][l]=m=m<<24^m>>>8}}for(e=
0;e<5;e++){a[e]=a[e].slice(0);b[e]=b[e].slice(0)}},F:function(a,b){if(a.length!==4)throw new sjcl.exception.invalid("invalid aes block size");var c=this.a[b],d=a[0]^c[0],e=a[b?3:1]^c[1],f=a[2]^c[2];a=a[b?1:3]^c[3];var g,h,i,k=c.length/4-2,j,l=4,m=[0,0,0,0];g=this.h[b];var n=g[0],o=g[1],p=g[2],q=g[3],r=g[4];for(j=0;j<k;j++){g=n[d>>>24]^o[e>>16&255]^p[f>>8&255]^q[a&255]^c[l];h=n[e>>>24]^o[f>>16&255]^p[a>>8&255]^q[d&255]^c[l+1];i=n[f>>>24]^o[a>>16&255]^p[d>>8&255]^q[e&255]^c[l+2];a=n[a>>>24]^o[d>>16&
255]^p[e>>8&255]^q[f&255]^c[l+3];l+=4;d=g;e=h;f=i}for(j=0;j<4;j++){m[b?3&-j:j]=r[d>>>24]<<24^r[e>>16&255]<<16^r[f>>8&255]<<8^r[a&255]^c[l++];g=d;d=e;e=f;f=a;a=g}return m}};
sjcl.bitArray={bitSlice:function(a,b,c){a=sjcl.bitArray.N(a.slice(b/32),32-(b&31)).slice(1);return c===undefined?a:sjcl.bitArray.clamp(a,c-b)},extract:function(a,b,c){var d=Math.floor(-b-c&31);return((b+c-1^b)&-32?a[b/32|0]<<32-d^a[b/32+1|0]>>>d:a[b/32|0]>>>d)&(1<<c)-1},concat:function(a,b){if(a.length===0||b.length===0)return a.concat(b);var c=a[a.length-1],d=sjcl.bitArray.getPartial(c);return d===32?a.concat(b):sjcl.bitArray.N(b,d,c|0,a.slice(0,a.length-1))},bitLength:function(a){var b=a.length;
if(b===0)return 0;return(b-1)*32+sjcl.bitArray.getPartial(a[b-1])},clamp:function(a,b){if(a.length*32<b)return a;a=a.slice(0,Math.ceil(b/32));var c=a.length;b&=31;if(c>0&&b)a[c-1]=sjcl.bitArray.partial(b,a[c-1]&2147483648>>b-1,1);return a},partial:function(a,b,c){if(a===32)return b;return(c?b|0:b<<32-a)+a*0x10000000000},getPartial:function(a){return Math.round(a/0x10000000000)||32},equal:function(a,b){if(sjcl.bitArray.bitLength(a)!==sjcl.bitArray.bitLength(b))return false;var c=0,d;for(d=0;d<a.length;d++)c|=
a[d]^b[d];return c===0},N:function(a,b,c,d){var e;e=0;if(d===undefined)d=[];for(;b>=32;b-=32){d.push(c);c=0}if(b===0)return d.concat(a);for(e=0;e<a.length;e++){d.push(c|a[e]>>>b);c=a[e]<<32-b}e=a.length?a[a.length-1]:0;a=sjcl.bitArray.getPartial(e);d.push(sjcl.bitArray.partial(b+a&31,b+a>32?c:d.pop(),1));return d},O:function(a,b){return[a[0]^b[0],a[1]^b[1],a[2]^b[2],a[3]^b[3]]}};
sjcl.codec.utf8String={fromBits:function(a){var b="",c=sjcl.bitArray.bitLength(a),d,e;for(d=0;d<c/8;d++){if((d&3)===0)e=a[d/4];b+=String.fromCharCode(e>>>24);e<<=8}return decodeURIComponent(escape(b))},toBits:function(a){a=unescape(encodeURIComponent(a));var b=[],c,d=0;for(c=0;c<a.length;c++){d=d<<8|a.charCodeAt(c);if((c&3)===3){b.push(d);d=0}}c&3&&b.push(sjcl.bitArray.partial(8*(c&3),d));return b}};
sjcl.codec.base64={B:"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/",fromBits:function(a,b,c){var d="",e=0,f=sjcl.codec.base64.B,g=0,h=sjcl.bitArray.bitLength(a);if(c)f=f.substr(0,62)+"-_";for(c=0;d.length*6<h;){d+=f.charAt((g^a[c]>>>e)>>>26);if(e<6){g=a[c]<<6-e;e+=26;c++}else{g<<=6;e-=6}}for(;d.length&3&&!b;)d+="=";return d},toBits:function(a,b){a=a.replace(/\s|=/g,"");var c=[],d=0,e=sjcl.codec.base64.B,f=0,g;if(b)e=e.substr(0,62)+"-_";for(b=0;b<a.length;b++){g=e.indexOf(a.charAt(b));
if(g<0)throw new sjcl.exception.invalid("this isn't base64!");if(d>26){d-=26;c.push(f^g>>>d);f=g<<32-d}else{d+=6;f^=g<<32-d}}d&56&&c.push(sjcl.bitArray.partial(d&56,f,1));return c}};sjcl.codec.base64url={fromBits:function(a){return sjcl.codec.base64.fromBits(a,1,1)},toBits:function(a){return sjcl.codec.base64.toBits(a,1)}};sjcl.hash.sha256=function(a){this.a[0]||this.u();if(a){this.m=a.m.slice(0);this.i=a.i.slice(0);this.e=a.e}else this.reset()};sjcl.hash.sha256.hash=function(a){return(new sjcl.hash.sha256).update(a).finalize()};
sjcl.hash.sha256.prototype={blockSize:512,reset:function(){this.m=this.L.slice(0);this.i=[];this.e=0;return this},update:function(a){if(typeof a==="string")a=sjcl.codec.utf8String.toBits(a);var b,c=this.i=sjcl.bitArray.concat(this.i,a);b=this.e;a=this.e=b+sjcl.bitArray.bitLength(a);for(b=512+b&-512;b<=a;b+=512)this.A(c.splice(0,16));return this},finalize:function(){var a,b=this.i,c=this.m;b=sjcl.bitArray.concat(b,[sjcl.bitArray.partial(1,1)]);for(a=b.length+2;a&15;a++)b.push(0);b.push(Math.floor(this.e/
4294967296));for(b.push(this.e|0);b.length;)this.A(b.splice(0,16));this.reset();return c},L:[],a:[],u:function(){function a(e){return(e-Math.floor(e))*0x100000000|0}var b=0,c=2,d;a:for(;b<64;c++){for(d=2;d*d<=c;d++)if(c%d===0)continue a;if(b<8)this.L[b]=a(Math.pow(c,0.5));this.a[b]=a(Math.pow(c,1/3));b++}},A:function(a){var b,c,d=a.slice(0),e=this.m,f=this.a,g=e[0],h=e[1],i=e[2],k=e[3],j=e[4],l=e[5],m=e[6],n=e[7];for(a=0;a<64;a++){if(a<16)b=d[a];else{b=d[a+1&15];c=d[a+14&15];b=d[a&15]=(b>>>7^b>>>18^
b>>>3^b<<25^b<<14)+(c>>>17^c>>>19^c>>>10^c<<15^c<<13)+d[a&15]+d[a+9&15]|0}b=b+n+(j>>>6^j>>>11^j>>>25^j<<26^j<<21^j<<7)+(m^j&(l^m))+f[a];n=m;m=l;l=j;j=k+b|0;k=i;i=h;h=g;g=b+(h&i^k&(h^i))+(h>>>2^h>>>13^h>>>22^h<<30^h<<19^h<<10)|0}e[0]=e[0]+g|0;e[1]=e[1]+h|0;e[2]=e[2]+i|0;e[3]=e[3]+k|0;e[4]=e[4]+j|0;e[5]=e[5]+l|0;e[6]=e[6]+m|0;e[7]=e[7]+n|0}};
sjcl.mode.ccm={name:"ccm",encrypt:function(a,b,c,d,e){var f,g=b.slice(0),h=sjcl.bitArray,i=h.bitLength(c)/8,k=h.bitLength(g)/8;e=e||64;d=d||[];if(i<7)throw new sjcl.exception.invalid("ccm: iv must be at least 7 bytes");for(f=2;f<4&&k>>>8*f;f++);if(f<15-i)f=15-i;c=h.clamp(c,8*(15-f));b=sjcl.mode.ccm.D(a,b,c,d,e,f);g=sjcl.mode.ccm.G(a,g,c,b,e,f);return h.concat(g.data,g.tag)},decrypt:function(a,b,c,d,e){e=e||64;d=d||[];var f=sjcl.bitArray,g=f.bitLength(c)/8,h=f.bitLength(b),i=f.clamp(b,h-e),k=f.bitSlice(b,
h-e);h=(h-e)/8;if(g<7)throw new sjcl.exception.invalid("ccm: iv must be at least 7 bytes");for(b=2;b<4&&h>>>8*b;b++);if(b<15-g)b=15-g;c=f.clamp(c,8*(15-b));i=sjcl.mode.ccm.G(a,i,c,k,e,b);a=sjcl.mode.ccm.D(a,i.data,c,d,e,b);if(!f.equal(i.tag,a))throw new sjcl.exception.corrupt("ccm: tag doesn't match");return i.data},D:function(a,b,c,d,e,f){var g=[],h=sjcl.bitArray,i=h.O;e/=8;if(e%2||e<4||e>16)throw new sjcl.exception.invalid("ccm: invalid tag length");if(d.length>0xffffffff||b.length>0xffffffff)throw new sjcl.exception.bug("ccm: can't deal with 4GiB or more data");
f=[h.partial(8,(d.length?64:0)|e-2<<2|f-1)];f=h.concat(f,c);f[3]|=h.bitLength(b)/8;f=a.encrypt(f);if(d.length){c=h.bitLength(d)/8;if(c<=65279)g=[h.partial(16,c)];else if(c<=0xffffffff)g=h.concat([h.partial(16,65534)],[c]);g=h.concat(g,d);for(d=0;d<g.length;d+=4)f=a.encrypt(i(f,g.slice(d,d+4).concat([0,0,0])))}for(d=0;d<b.length;d+=4)f=a.encrypt(i(f,b.slice(d,d+4).concat([0,0,0])));return h.clamp(f,e*8)},G:function(a,b,c,d,e,f){var g,h=sjcl.bitArray;g=h.O;var i=b.length,k=h.bitLength(b);c=h.concat([h.partial(8,
f-1)],c).concat([0,0,0]).slice(0,4);d=h.bitSlice(g(d,a.encrypt(c)),0,e);if(!i)return{tag:d,data:[]};for(g=0;g<i;g+=4){c[3]++;e=a.encrypt(c);b[g]^=e[0];b[g+1]^=e[1];b[g+2]^=e[2];b[g+3]^=e[3]}return{tag:d,data:h.clamp(b,k)}}};sjcl.misc.hmac=function(a,b){this.K=b=b||sjcl.hash.sha256;var c=[[],[]],d=b.prototype.blockSize/32;this.k=[new b,new b];if(a.length>d)a=b.hash(a);for(b=0;b<d;b++){c[0][b]=a[b]^909522486;c[1][b]=a[b]^1549556828}this.k[0].update(c[0]);this.k[1].update(c[1])};
sjcl.misc.hmac.prototype.encrypt=sjcl.misc.hmac.prototype.mac=function(a,b){a=(new this.K(this.k[0])).update(a,b).finalize();return(new this.K(this.k[1])).update(a).finalize()};
sjcl.misc.pbkdf2=function(a,b,c,d,e){c=c||1E3;if(d<0||c<0)throw sjcl.exception.invalid("invalid params to pbkdf2");if(typeof a==="string")a=sjcl.codec.utf8String.toBits(a);e=e||sjcl.misc.hmac;a=new e(a);var f,g,h,i,k=[],j=sjcl.bitArray;for(i=1;32*k.length<(d||1);i++){e=f=a.encrypt(j.concat(b,[i]));for(g=1;g<c;g++){f=a.encrypt(f);for(h=0;h<f.length;h++)e[h]^=f[h]}k=k.concat(e)}if(d)k=j.clamp(k,d);return k};
sjcl.random={randomWords:function(a,b){var c=[];b=this.isReady(b);var d;if(b===0)throw new sjcl.exception.notReady("generator isn't seeded");else b&2&&this.T(!(b&1));for(b=0;b<a;b+=4){(b+1)%0x10000===0&&this.J();d=this.t();c.push(d[0],d[1],d[2],d[3])}this.J();return c.slice(0,a)},setDefaultParanoia:function(a){this.s=a},addEntropy:function(a,b,c){c=c||"user";var d,e,f=(new Date).valueOf(),g=this.p[c],h=this.isReady();d=this.C[c];if(d===undefined)d=this.C[c]=this.Q++;if(g===undefined)g=this.p[c]=0;this.p[c]=
(this.p[c]+1)%this.b.length;switch(typeof a){case "number":break;case "object":if(b===undefined)for(c=b=0;c<a.length;c++)for(e=a[c];e>0;){b++;e>>>=1}this.b[g].update([d,this.H++,2,b,f,a.length].concat(a));break;case "string":if(b===undefined)b=a.length;this.b[g].update([d,this.H++,3,b,f,a.length]);this.b[g].update(a);break;default:throw new sjcl.exception.bug("random: addEntropy only supports number, array or string");}this.j[g]+=b;this.f+=b;if(h===0){this.isReady()!==0&&this.I("seeded",Math.max(this.g,
this.f));this.I("progress",this.getProgress())}},isReady:function(a){a=this.z[a!==undefined?a:this.s];return this.g&&this.g>=a?this.j[0]>80&&(new Date).valueOf()>this.M?3:1:this.f>=a?2:0},getProgress:function(a){a=this.z[a?a:this.s];return this.g>=a?1["0"]:this.f>a?1["0"]:this.f/a},startCollectors:function(){if(!this.l){if(window.addEventListener){window.addEventListener("load",this.n,false);window.addEventListener("mousemove",this.o,false)}else if(document.attachEvent){document.attachEvent("onload",
this.n);document.attachEvent("onmousemove",this.o)}else throw new sjcl.exception.bug("can't attach event");this.l=true}},stopCollectors:function(){if(this.l){if(window.removeEventListener){window.removeEventListener("load",this.n,false);window.removeEventListener("mousemove",this.o,false)}else if(window.detachEvent){window.detachEvent("onload",this.n);window.detachEvent("onmousemove",this.o)}this.l=false}},addEventListener:function(a,b){this.q[a][this.P++]=b},removeEventListener:function(a,b){var c;
a=this.q[a];var d=[];for(c in a)a.hasOwnProperty(c)&&a[c]===b&&d.push(c);for(b=0;b<d.length;b++){c=d[b];delete a[c]}},b:[new sjcl.hash.sha256],j:[0],w:0,p:{},H:0,C:{},Q:0,g:0,f:0,M:0,a:[0,0,0,0,0,0,0,0],d:[0,0,0,0],r:undefined,s:6,l:false,q:{progress:{},seeded:{}},P:0,z:[0,48,64,96,128,192,0x100,384,512,768,1024],t:function(){for(var a=0;a<4;a++){this.d[a]=this.d[a]+1|0;if(this.d[a])break}return this.r.encrypt(this.d)},J:function(){this.a=this.t().concat(this.t());this.r=new sjcl.cipher.aes(this.a)},
S:function(a){this.a=sjcl.hash.sha256.hash(this.a.concat(a));this.r=new sjcl.cipher.aes(this.a);for(a=0;a<4;a++){this.d[a]=this.d[a]+1|0;if(this.d[a])break}},T:function(a){var b=[],c=0,d;this.M=b[0]=(new Date).valueOf()+3E4;for(d=0;d<16;d++)b.push(Math.random()*0x100000000|0);for(d=0;d<this.b.length;d++){b=b.concat(this.b[d].finalize());c+=this.j[d];this.j[d]=0;if(!a&&this.w&1<<d)break}if(this.w>=1<<this.b.length){this.b.push(new sjcl.hash.sha256);this.j.push(0)}this.f-=c;if(c>this.g)this.g=c;this.w++;
this.S(b)},o:function(a){sjcl.random.addEntropy([a.x||a.clientX||a.offsetX,a.y||a.clientY||a.offsetY],2,"mouse")},n:function(){sjcl.random.addEntropy(new Date,2,"loadtime")},I:function(a,b){var c;a=sjcl.random.q[a];var d=[];for(c in a)a.hasOwnProperty(c)&&d.push(a[c]);for(c=0;c<d.length;c++)d[c](b)}};try{var s=new Uint32Array(32);crypto.getRandomValues(s);sjcl.random.addEntropy(s,1024,"crypto['getRandomValues']")}catch(t){}
sjcl.json={defaults:{v:1,iter:1E3,ks:128,ts:64,mode:"ccm",adata:"",cipher:"aes"},encrypt:function(a,b,c,d){c=c||{};d=d||{};var e=sjcl.json,f=e.c({iv:sjcl.random.randomWords(4,0)},e.defaults);e.c(f,c);if(typeof f.salt==="string")f.salt=sjcl.codec.base64.toBits(f.salt);if(typeof f.iv==="string")f.iv=sjcl.codec.base64.toBits(f.iv);if(!sjcl.mode[f.mode]||!sjcl.cipher[f.cipher]||typeof a==="string"&&f.iter<=100||f.ts!==64&&f.ts!==96&&f.ts!==128||f.ks!==128&&f.ks!==192&&f.ks!==0x100||f.iv.length<2||f.iv.length>
4)throw new sjcl.exception.invalid("json encrypt: invalid parameters");if(typeof a==="string"){c=sjcl.misc.cachedPbkdf2(a,f);a=c.key.slice(0,f.ks/32);f.salt=c.salt}if(typeof b==="string")b=sjcl.codec.utf8String.toBits(b);c=new sjcl.cipher[f.cipher](a);e.c(d,f);d.key=a;f.ct=sjcl.mode[f.mode].encrypt(c,b,f.iv,f.adata,f.ts);return e.encode(e.U(f,e.defaults))},decrypt:function(a,b,c,d){c=c||{};d=d||{};var e=sjcl.json;b=e.c(e.c(e.c({},e.defaults),e.decode(b)),c,true);if(typeof b.salt==="string")b.salt=
sjcl.codec.base64.toBits(b.salt);if(typeof b.iv==="string")b.iv=sjcl.codec.base64.toBits(b.iv);if(!sjcl.mode[b.mode]||!sjcl.cipher[b.cipher]||typeof a==="string"&&b.iter<=100||b.ts!==64&&b.ts!==96&&b.ts!==128||b.ks!==128&&b.ks!==192&&b.ks!==0x100||!b.iv||b.iv.length<2||b.iv.length>4)throw new sjcl.exception.invalid("json decrypt: invalid parameters");if(typeof a==="string"){c=sjcl.misc.cachedPbkdf2(a,b);a=c.key.slice(0,b.ks/32);b.salt=c.salt}c=new sjcl.cipher[b.cipher](a);c=sjcl.mode[b.mode].decrypt(c,
b.ct,b.iv,b.adata,b.ts);e.c(d,b);d.key=a;return sjcl.codec.utf8String.fromBits(c)},encode:function(a){var b,c="{",d="";for(b in a)if(a.hasOwnProperty(b)){if(!b.match(/^[a-z0-9]+$/i))throw new sjcl.exception.invalid("json encode: invalid property name");c+=d+b+":";d=",";switch(typeof a[b]){case "number":case "boolean":c+=a[b];break;case "string":c+='"'+escape(a[b])+'"';break;case "object":c+='"'+sjcl.codec.base64.fromBits(a[b],1)+'"';break;default:throw new sjcl.exception.bug("json encode: unsupported type");
}}return c+"}"},decode:function(a){a=a.replace(/\s/g,"");if(!a.match(/^\{.*\}$/))throw new sjcl.exception.invalid("json decode: this isn't json!");a=a.replace(/^\{|\}$/g,"").split(/,/);var b={},c,d;for(c=0;c<a.length;c++){if(!(d=a[c].match(/^([a-z][a-z0-9]*):(?:(\d+)|"([a-z0-9+\/%*_.@=\-]*)")$/i)))throw new sjcl.exception.invalid("json decode: this isn't json!");b[d[1]]=d[2]?parseInt(d[2],10):d[1].match(/^(ct|salt|iv)$/)?sjcl.codec.base64.toBits(d[3]):unescape(d[3])}return b},c:function(a,b,c){if(a===
undefined)a={};if(b===undefined)return a;var d;for(d in b)if(b.hasOwnProperty(d)){if(c&&a[d]!==undefined&&a[d]!==b[d])throw new sjcl.exception.invalid("required parameter overridden");a[d]=b[d]}return a},U:function(a,b){var c={},d;for(d in a)if(a.hasOwnProperty(d)&&a[d]!==b[d])c[d]=a[d];return c},V:function(a,b){var c={},d;for(d=0;d<b.length;d++)if(a[b[d]]!==undefined)c[b[d]]=a[b[d]];return c}};sjcl.encrypt=sjcl.json.encrypt;sjcl.decrypt=sjcl.json.decrypt;sjcl.misc.R={};
sjcl.misc.cachedPbkdf2=function(a,b){var c=sjcl.misc.R,d;b=b||{};d=b.iter||1E3;c=c[a]=c[a]||{};d=c[d]=c[d]||{firstSalt:b.salt&&b.salt.length?b.salt.slice(0):sjcl.random.randomWords(2,0)};c=b.salt===undefined?d.firstSalt:b.salt;d[c]=d[c]||sjcl.misc.pbkdf2(a,c,b.iter);return{key:d[c].slice(0),salt:c.slice(0)}};

    /* Cryptlet
     *
     *
     */

    //
    // Constant Definitions
    //
    var containerClass = 'cryptlet-container',
    minPasswordLength = 8,
    startBlock = '===start=cryptlet===',
    endBlock = '===end=cryptlet===',

    //
    // Find elements on the page
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
      * Remove trailing whitespace.
      */
    trim = function( text ) {
        return text.replace(/[\s\r\n]+$/, '');
    },

    /**
      * Return true if the text is already encrypted by cryptlet, false otherwise.
      */
    isEncrypted = function( text ) {
        return text.slice( 0, startBlock.length ) === startBlock &&
            text.slice( -endBlock.length ) === endBlock;
    },

    /**
      * Encrypt the body of your gmail message.
      */
    encrypt = function () {

        var bodyTextarea = gmailDoc.getElementsByName('body')[0];// Find the body textarea
        if ( isEncrypted( trim( bodyTextarea.value ) )) {
            fail( 'You have already encrypted this text.' );
        }

        var password = prompt('Enter a password, please!');
        if( typeof password === 'undefined' || password === null) {
            return; // they cancelled.
        } else if( password === '') {
            fail( 'You must enter a password.' );
        } else if( password.length < minPasswordLength ) {
            fail( 'You must enter a longer password.' );
        }

        var encrypted = startBlock +
            sjcl.encrypt(password, bodyTextarea.value)
            + endBlock;
        bodyTextarea.value = encrypted;
    },

    /**
      * Decrypt the content of a div that is the first element of the parent of the caller.
      */
    decrypt = function ( ) {
        var password = prompt('Enter a password, please!');

        if( password === '' || typeof password === 'undefined' || password === null ) {
            return; // no password entered.
        }

        var textElement = this.parentNode.firstChild,
        trimmed = trim( textElement.textContent );
        if( !isEncrypted( trimmed )) {
            fail( 'This text is not encrypted.' );
        }

        try {
            // Chop off the start and end blocks.
            var rawText = trimmed.slice(startBlock.length, -endBlock.length);
            textElement.innerText = sjcl.decrypt(password, rawText);
            // Remove the element, since we have decrypted.
            this.parentNode.removeChild( this );
        } catch(err) {
            fail( 'Wrong password: ' + err );
        }
    },

    /**
      * Add an `encrypt' button for composition.
      */
    buildComposeInterface = function() {
        var divElements = gmailDoc.getElementsByTagName('div'),
        discardButton = null;

        // Find the div with text 'Discard'.
        for( var i = 0 ; i < divElements.length ; i ++ ) {
            // Is a text node.
            var div = divElements[i];
            if( typeof div.firstChild !== 'undefined' && div.firstChild !== null ) { // is this the best way to detect absence of child?
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

        // Return if there was no discard button.
        if( discardButton === null ) {
            return;
        }

        // Return if there's already an encrypt button for this container.
        if( discardButton.parentNode.getElementsByClassName( containerClass ).length > 0 ) {
            return;
        }

        // Generate the interface elements
        var containerSpan = gmailDoc.createElement( 'span' ),
        encryptButton = gmailDoc.createElement( 'div' );

        // Set up container div
        containerSpan.className = containerClass;

        // Set up encrypt button
        encryptButton.setAttribute('role', 'button'); // necessary?
        encryptButton.className = discardButton.className; // copy styling
        encryptButton.appendChild( gmailDoc.createTextNode( 'Encrypt' )); // set text
        encryptButton.onclick = encrypt; // call 'encrypt' on click

        // Lay it on down brother
        containerSpan.appendChild( encryptButton );

        discardButton.parentNode.insertBefore( containerSpan ); // insert before the discard button
    },

    /**
      * Add a 'decrypt' button for message content.
      */
    buildInboxInterface = function() {
        var divElements = gmailDoc.getElementsByTagName('div'),
        mainDiv = null,
        buttonClass = null;

        // Find main div from role attribute
        for( var i = 0 ; i < divElements.length ; i++ ) {
            if(divElements[i].getAttribute( 'role' ) === 'main' ) {
                mainDiv = divElements[i];
                break;
            }
        }

        // Find divs with text from inside main div with text starting with
        // startBlock and ending with endBlock.
        var divs = mainDiv.getElementsByTagName('div'),
        encryptedDivs = []; // push divs with text onto this

        for( var i = 0 ; i < divs.length ; i++ ) {
            var div = divs.item(i);
            if( div.parentNode.getElementsByClassName( containerClass ).length > 0 ) {
                continue; // continue if this div already has a button
            }
            if( typeof div.firstChild !== 'undefined' && div.firstChild !== null ) {
                if(div.firstChild.nodeType === 3) {
                    var text = div.textContent;
                    if( typeof text !== 'undefined' && text !== null ) {
                        if( isEncrypted( trim( text ) )) {
                            encryptedDivs.push( div );
                        }
                    }
                }
            }
        }

        // Add decrypt button to matching divs.
        for( var i = 0 ; i < encryptedDivs.length ; i++ ) {
            var containerSpan = gmailDoc.createElement( 'span' ),
            decryptButton = gmailDoc.createElement( 'span' );

            containerSpan.setAttribute('style', 'cursor: pointer; margin: 1em; padding: .5em; background: black; color: white');

            containerSpan.className = containerClass;
            containerSpan.appendChild(decryptButton);

            decryptButton.appendChild( document.createTextNode('Decrypt') );
            decryptButton.setAttribute( 'role', 'button' );

            containerSpan.onclick = decrypt; // handler to decrypt

            encryptedDivs[i].parentNode.insertBefore(containerSpan);

        }
    },

    /**
      * Handle hash changes, keeping the interface fresh.
      */
    hashChangeHandler = function() {
        // var curFragment = document.location.hash,

        buildComposeInterface();
        buildInboxInterface();
    };

    // Keep us fresh.  It all dies on reload, though.
    window.onhashchange = hashChangeHandler;

    // Google rebuilds the change after certain clicks.  Catch these
    // events on the capture (way down) because they won't bubble back
    // up.
    gmailDoc.addEventListener('click', hashChangeHandler, true);
})();
