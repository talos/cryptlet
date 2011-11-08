#!/usr/bin/env bash

all:
	uglifyjs -nc  cryptlet.js > cryptlet.min.js
	node -e "var fs = require('fs'); console.log('javascript:' + encodeURIComponent(fs.readFileSync('cryptlet.min.js', 'ascii')));" > cryptlet.bookmarklet

clean:
	rm cryptlet.min.js
	rm cryptlet.bookmarklet