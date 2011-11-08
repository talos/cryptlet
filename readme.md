# Cryptlet :: A little bit 'o' privacy for Gmail in a bookmarklet.

### What it does

Provides very basic, insecure encryption and decryption in [Gmail](http://www.gmail.com/), through a bookmarklet.  Uses the [Stanford Javascript Crypto Library](http://bitwiseshiftleft.github.com/sjcl/).

### Usage

* __Safari__ : Paste the [bookmarklet](cryptlet/blob/master/cryptlet.bookmarklet) into the URL bar after navigating to [Gmail](http://www.gmail.com/).  Alternatively, add it as a bookmark and hit it after navigating to [Gmail](http://www.gmail.com/).
* __Chrome__ : Add the [bookmarklet](cryptlet/blob/master/cryptlet.bookmarklet) as a bookmark and hit it after navigating to [Gmail](http://www.gmail.com/).  Chrome doesn't support pasting a bookmarklet this long.
* __Firefox__: Not supported. Yet.

### Is this a good way to secure my email?

_Absolutely not_.  *Do NOT use this to secure your email.*  You should use PGP and a non-webmail client for actual security.  Ideally, cryptlet is 'kinda neat'.  Nothing more.

### Building / Requirements

After editing `cryptlet.js`, you can regenerate `cryptlet.bookmarklet` by running `make`.  You will need an installation of [node.js](http://nodejs.org/) and [uglifyjs](https://github.com/mishoo/UglifyJS).