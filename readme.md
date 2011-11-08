# Cryptlet :: A little bit 'o' privacy for Gmail in a bookmarklet.

### What it does

Provides very basic, insecure encryption and decryption in [Gmail](http://www.gmail.com/), through a bookmarklet.  Uses the [Stanford Javascript Crypto Library](http://bitwiseshiftleft.github.com/sjcl/).

### Usage

* __Safari__ : Paste the [bookmarklet](cryptlet/blob/master/cryptlet.bookmarklet) into the URL bar after navigating to [Gmail](http://www.gmail.com/).  Alternatively, add it as a bookmark and hit it after navigating to [Gmail](http://www.gmail.com/).
* __Chrome__ : Add the [bookmarklet](cryptlet/blob/master/cryptlet.bookmarklet) as a bookmark and hit it after navigating to [Gmail](http://www.gmail.com/).  Chrome doesn't support pasting a bookmarklet this long.
* __Firefox__: Not supported. Yet.

__To encrypt__: Navigate to compose, and click the "Encrypt" button before sending your mail.  Enter in a good password.  Don't forget it, because the body will disappear.  Yes, Gmail's auto-save renders is one of many security flaws.

__To decrypt__: You'll notice that emails now have a "Decrypt" link at the end of their text.  If you received an encrypted email, click "Decrypt" and enter the password it was encrypted with.  If you enter the right password, you will see the original message.  The decrypted message will not persist if you navigate away from the page.

### Is this a good way to secure my email?

_Absolutely not_.  __Do *NOT* use this to secure your email.__  You should use PGP and a non-webmail client for actual security.  Ideally, cryptlet is 'kinda neat'.  Nothing more.

### Building / Requirements

After editing `cryptlet.js`, you can regenerate `cryptlet.bookmarklet` by running `make`.  You will need an installation of [node.js](http://nodejs.org/) and [uglifyjs](https://github.com/mishoo/UglifyJS).