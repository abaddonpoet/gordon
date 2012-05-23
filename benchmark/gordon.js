/*
 *    Gordon: An open source Flash™ runtime written in pure JavaScript
 *
 *    Copyright (c) 2010 Tobias Schneider
 *    Gordon is freely distributable under the terms of the MIT license.
 */

(function(window, undefined){
    (function (GLOBAL) {
        /*
         * Port of script by Masanao Izumo.
         *
         * Wrapped all the variables in a function, created a
         * constructor for interacting with the lib. Everything
         * else was written by M. Izumo.
         *
         * Original code can be found here: http://www.onicos.com/staff/iz/amuse/javascript/expert/inflate.txt
         *
         */
    
        var zip_WSIZE = 32768;		// Sliding Window size
        var zip_STORED_BLOCK = 0;
        var zip_STATIC_TREES = 1;
        var zip_DYN_TREES    = 2;
    
        /* for inflate */
        var zip_lbits = 9; 		// bits in base literal/length lookup table
        var zip_dbits = 6; 		// bits in base distance lookup table
        var zip_INBUFSIZ = 32768;	// Input buffer size
        var zip_INBUF_EXTRA = 64;	// Extra buffer
    
        /* variables (inflate) */
        var zip_slide;
        var zip_wp;			// current position in slide
        var zip_fixed_tl = null;	// inflate static
        var zip_fixed_td;		// inflate static
        var zip_fixed_bl, fixed_bd;	// inflate static
        var zip_bit_buf;		// bit buffer
        var zip_bit_len;		// bits in bit buffer
        var zip_method;
        var zip_eof;
        var zip_copy_leng;
        var zip_copy_dist;
        var zip_tl, zip_td;	// literal/length and distance decoder tables
        var zip_bl, zip_bd;	// number of bits decoded by tl and td
    
        var zip_inflate_data;
        var zip_inflate_pos;
    
    
        /* constant tables (inflate) */
        var zip_MASK_BITS = new Array(
            0x0000,
            0x0001, 0x0003, 0x0007, 0x000f, 0x001f, 0x003f, 0x007f, 0x00ff,
            0x01ff, 0x03ff, 0x07ff, 0x0fff, 0x1fff, 0x3fff, 0x7fff, 0xffff);
        // Tables for deflate from PKZIP's appnote.txt.
        var zip_cplens = new Array( // Copy lengths for literal codes 257..285
            3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
            35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258, 0, 0);
        /* note: see note #13 above about the 258 in this list. */
        var zip_cplext = new Array( // Extra bits for literal codes 257..285
            0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2,
            3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0, 99, 99); // 99==invalid
        var zip_cpdist = new Array( // Copy offsets for distance codes 0..29
            1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
            257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145,
            8193, 12289, 16385, 24577);
        var zip_cpdext = new Array( // Extra bits for distance codes
            0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6,
            7, 7, 8, 8, 9, 9, 10, 10, 11, 11,
            12, 12, 13, 13);
        var zip_border = new Array(  // Order of the bit length code lengths
            16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15);
        /* objects (inflate) */
    
        function zip_HuftList() {
            this.next = null;
            this.list = null;
        }
    
        function zip_HuftNode() {
            this.e = 0; // number of extra bits or operation
            this.b = 0; // number of bits in this code or subcode
    
            // union
            this.n = 0; // literal, length base, or distance base
            this.t = null; // (zip_HuftNode) pointer to next level of table
        }
    
        function zip_HuftBuild(b,	// code lengths in bits (all assumed <= BMAX)
                               n,	// number of codes (assumed <= N_MAX)
                               s,	// number of simple-valued codes (0..s-1)
                               d,	// list of base values for non-simple codes
                               e,	// list of extra bits for non-simple codes
                               mm	// maximum lookup bits
                              ) {
            this.BMAX = 16;   // maximum bit length of any code
            this.N_MAX = 288; // maximum number of codes in any set
            this.status = 0;	// 0: success, 1: incomplete table, 2: bad input
            this.root = null;	// (zip_HuftList) starting table
            this.m = 0;		// maximum lookup bits, returns actual
    
            /* Given a list of code lengths and a maximum table size, make a set of
               tables to decode that set of codes.	Return zero on success, one if
               the given code set is incomplete (the tables are still built in this
               case), two if the input is invalid (all zero length codes or an
               oversubscribed set of lengths), and three if not enough memory.
               The code with value 256 is special, and the tables are constructed
               so that no bits beyond that code are fetched when that code is
               decoded. */
            {
                var a;			// counter for codes of length k
                var c = new Array(this.BMAX+1);	// bit length count table
                var el;			// length of EOB code (value 256)
                var f;			// i repeats in table every f entries
                var g;			// maximum code length
                var h;			// table level
                var i;			// counter, current code
                var j;			// counter
                var k;			// number of bits in current code
                var lx = new Array(this.BMAX+1);	// stack of bits per table
                var p;			// pointer into c[], b[], or v[]
                var pidx;		// index of p
                var q;			// (zip_HuftNode) points to current table
                var r = new zip_HuftNode(); // table entry for structure assignment
                var u = new Array(this.BMAX); // zip_HuftNode[BMAX][]  table stack
                var v = new Array(this.N_MAX); // values in order of bit length
                var w;
                var x = new Array(this.BMAX+1);// bit offsets, then code stack
                var xp;			// pointer into x or c
                var y;			// number of dummy codes added
                var z;			// number of entries in current table
                var o;
                var tail;		// (zip_HuftList)
    
                tail = this.root = null;
                for(i = 0; i < c.length; i++)
                    c[i] = 0;
                for(i = 0; i < lx.length; i++)
                    lx[i] = 0;
                for(i = 0; i < u.length; i++)
                    u[i] = null;
                for(i = 0; i < v.length; i++)
                    v[i] = 0;
                for(i = 0; i < x.length; i++)
                    x[i] = 0;
    
                // Generate counts for each bit length
                el = n > 256 ? b[256] : this.BMAX; // set length of EOB code, if any
                p = b; pidx = 0;
                i = n;
                do {
                    c[p[pidx]]++;	// assume all entries <= BMAX
                    pidx++;
                } while(--i > 0);
                if(c[0] == n) {	// null input--all zero length codes
                    this.root = null;
                    this.m = 0;
                    this.status = 0;
                    return;
                }
    
                // Find minimum and maximum length, bound *m by those
                for(j = 1; j <= this.BMAX; j++)
                    if(c[j] != 0)
                        break;
                k = j;			// minimum code length
                if(mm < j)
                    mm = j;
                for(i = this.BMAX; i != 0; i--)
                    if(c[i] != 0)
                        break;
                g = i;			// maximum code length
                if(mm > i)
                    mm = i;
    
                // Adjust last length count to fill out codes, if needed
                for(y = 1 << j; j < i; j++, y <<= 1)
                    if((y -= c[j]) < 0) {
                        this.status = 2;	// bad input: more codes than bits
                        this.m = mm;
                        return;
                    }
                if((y -= c[i]) < 0) {
                    this.status = 2;
                    this.m = mm;
                    return;
                }
                c[i] += y;
    
                // Generate starting offsets into the value table for each length
                x[1] = j = 0;
                p = c;
                pidx = 1;
                xp = 2;
                while(--i > 0)		// note that i == g from above
                    x[xp++] = (j += p[pidx++]);
    
                // Make a table of values in order of bit lengths
                p = b; pidx = 0;
                i = 0;
                do {
                    if((j = p[pidx++]) != 0)
                        v[x[j]++] = i;
                } while(++i < n);
                n = x[g];			// set n to length of v
    
                // Generate the Huffman codes and for each, make the table entries
                x[0] = i = 0;		// first Huffman code is zero
                p = v; pidx = 0;		// grab values in bit order
                h = -1;			// no tables yet--level -1
                w = lx[0] = 0;		// no bits decoded yet
                q = null;			// ditto
                z = 0;			// ditto
    
                // go through the bit lengths (k already is bits in shortest code)
                for(; k <= g; k++) {
                    a = c[k];
                    while(a-- > 0) {
                        // here i is the Huffman code of length k bits for value p[pidx]
                        // make tables up to required level
                        while(k > w + lx[1 + h]) {
                            w += lx[1 + h]; // add bits already decoded
                            h++;
    
                            // compute minimum size table less than or equal to *m bits
                            z = (z = g - w) > mm ? mm : z; // upper limit
                            if((f = 1 << (j = k - w)) > a + 1) { // try a k-w bit table
                                // too few codes for k-w bit table
                                f -= a + 1;	// deduct codes from patterns left
                                xp = k;
                                while(++j < z) { // try smaller tables up to z bits
                                    if((f <<= 1) <= c[++xp])
                                        break;	// enough codes to use up j bits
                                    f -= c[xp];	// else deduct codes from patterns
                                }
                            }
                            if(w + j > el && w < el)
                                j = el - w;	// make EOB code end at table
                            z = 1 << j;	// table entries for j-bit table
                            lx[1 + h] = j; // set table size in stack
    
                            // allocate and link in new table
                            q = new Array(z);
                            for(o = 0; o < z; o++) {
                                q[o] = new zip_HuftNode();
                            }
    
                            if(tail == null)
                                tail = this.root = new zip_HuftList();
                            else
                                tail = tail.next = new zip_HuftList();
                            tail.next = null;
                            tail.list = q;
                            u[h] = q;	// table starts after link
    
                            /* connect to last table, if there is one */
                            if(h > 0) {
                                x[h] = i;		// save pattern for backing up
                                r.b = lx[h];	// bits to dump before this table
                                r.e = 16 + j;	// bits in this table
                                r.t = q;		// pointer to this table
                                j = (i & ((1 << w) - 1)) >> (w - lx[h]);
                                u[h-1][j].e = r.e;
                                u[h-1][j].b = r.b;
                                u[h-1][j].n = r.n;
                                u[h-1][j].t = r.t;
                            }
                        }
    
                        // set up table entry in r
                        r.b = k - w;
                        if(pidx >= n)
                            r.e = 99;		// out of values--invalid code
                        else if(p[pidx] < s) {
                            r.e = (p[pidx] < 256 ? 16 : 15); // 256 is end-of-block code
                            r.n = p[pidx++];	// simple code is just the value
                        } else {
                            r.e = e[p[pidx] - s];	// non-simple--look up in lists
                            r.n = d[p[pidx++] - s];
                        }
    
                        // fill code-like entries with r //
                        f = 1 << (k - w);
                        for(j = i >> w; j < z; j += f) {
                            q[j].e = r.e;
                            q[j].b = r.b;
                            q[j].n = r.n;
                            q[j].t = r.t;
                        }
    
                        // backwards increment the k-bit code i
                        for(j = 1 << (k - 1); (i & j) != 0; j >>= 1)
                            i ^= j;
                        i ^= j;
    
                        // backup over finished tables
                        while((i & ((1 << w) - 1)) != x[h]) {
                            w -= lx[h];		// don't need to update q
                            h--;
                        }
                    }
                }
    
                /* return actual size of base table */
                this.m = lx[1];
    
                /* Return true (1) if we were given an incomplete table */
                this.status = ((y != 0 && g != 1) ? 1 : 0);
            } /* end of constructor */
        }
    
    
        /* routines (inflate) */
    
        function zip_GET_BYTE() {
            if(zip_inflate_data.length == zip_inflate_pos)
                return -1;
            return zip_inflate_data.charCodeAt(zip_inflate_pos++) & 0xff;
        }
    
        function zip_NEEDBITS(n) {
            while(zip_bit_len < n) {
                zip_bit_buf |= zip_GET_BYTE() << zip_bit_len;
                zip_bit_len += 8;
            }
        }
    
        function zip_GETBITS(n) {
            return zip_bit_buf & zip_MASK_BITS[n];
        }
    
        function zip_DUMPBITS(n) {
            zip_bit_buf >>= n;
            zip_bit_len -= n;
        }
    
        function zip_inflate_codes(buff, off, size) {
            /* inflate (decompress) the codes in a deflated (compressed) block.
               Return an error code or zero if it all goes ok. */
            var e;		// table entry flag/number of extra bits
            var t;		// (zip_HuftNode) pointer to table entry
            var n;
    
            if(size == 0)
                return 0;
    
            // inflate the coded data
            n = 0;
            for(;;) {			// do until end of block
                zip_NEEDBITS(zip_bl);
                t = zip_tl.list[zip_GETBITS(zip_bl)];
                e = t.e;
                while(e > 16) {
                    if(e == 99)
                        return -1;
                    zip_DUMPBITS(t.b);
                    e -= 16;
                    zip_NEEDBITS(e);
                    t = t.t[zip_GETBITS(e)];
                    e = t.e;
                }
                zip_DUMPBITS(t.b);
    
                if(e == 16) {		// then it's a literal
                    zip_wp &= zip_WSIZE - 1;
                    buff[off + n++] = zip_slide[zip_wp++] = t.n;
                    if(n == size)
                        return size;
                    continue;
                }
    
                // exit if end of block
                if(e == 15)
                    break;
    
                // it's an EOB or a length
    
                // get length of block to copy
                zip_NEEDBITS(e);
                zip_copy_leng = t.n + zip_GETBITS(e);
                zip_DUMPBITS(e);
    
                // decode distance of block to copy
                zip_NEEDBITS(zip_bd);
                t = zip_td.list[zip_GETBITS(zip_bd)];
                e = t.e;
    
                while(e > 16) {
                    if(e == 99)
                        return -1;
                    zip_DUMPBITS(t.b);
                    e -= 16;
                    zip_NEEDBITS(e);
                    t = t.t[zip_GETBITS(e)];
                    e = t.e;
                }
                zip_DUMPBITS(t.b);
                zip_NEEDBITS(e);
                zip_copy_dist = zip_wp - t.n - zip_GETBITS(e);
                zip_DUMPBITS(e);
    
                // do the copy
                while(zip_copy_leng > 0 && n < size) {
                    zip_copy_leng--;
                    zip_copy_dist &= zip_WSIZE - 1;
                    zip_wp &= zip_WSIZE - 1;
                    buff[off + n++] = zip_slide[zip_wp++]
                        = zip_slide[zip_copy_dist++];
                }
    
                if(n == size)
                    return size;
            }
    
            zip_method = -1; // done
            return n;
        }
    
        function zip_inflate_stored(buff, off, size) {
            /* "decompress" an inflated type 0 (stored) block. */
            var n;
    
            // go to byte boundary
            n = zip_bit_len & 7;
            zip_DUMPBITS(n);
    
            // get the length and its complement
            zip_NEEDBITS(16);
            n = zip_GETBITS(16);
            zip_DUMPBITS(16);
            zip_NEEDBITS(16);
            if(n != ((~zip_bit_buf) & 0xffff))
                return -1;			// error in compressed data
            zip_DUMPBITS(16);
    
            // read and output the compressed data
            zip_copy_leng = n;
    
            n = 0;
            while(zip_copy_leng > 0 && n < size) {
                zip_copy_leng--;
                zip_wp &= zip_WSIZE - 1;
                zip_NEEDBITS(8);
                buff[off + n++] = zip_slide[zip_wp++] =
                    zip_GETBITS(8);
                zip_DUMPBITS(8);
            }
    
            if(zip_copy_leng == 0)
                zip_method = -1; // done
            return n;
        }
    
        function zip_inflate_fixed(buff, off, size) {
            /* decompress an inflated type 1 (fixed Huffman codes) block.  We should
               either replace this with a custom decoder, or at least precompute the
               Huffman tables. */
    
            // if first time, set up tables for fixed blocks
            if(zip_fixed_tl == null) {
                var i;			// temporary variable
                var l = new Array(288);	// length list for huft_build
                var h;	// zip_HuftBuild
    
                // literal table
                for(i = 0; i < 144; i++)
                    l[i] = 8;
                for(; i < 256; i++)
                    l[i] = 9;
                for(; i < 280; i++)
                    l[i] = 7;
                for(; i < 288; i++)	// make a complete, but wrong code set
                    l[i] = 8;
                zip_fixed_bl = 7;
    
                h = new zip_HuftBuild(l, 288, 257, zip_cplens, zip_cplext,
                                      zip_fixed_bl);
                if(h.status != 0) {
                    alert("HufBuild error: "+h.status);
                    return -1;
                }
                zip_fixed_tl = h.root;
                zip_fixed_bl = h.m;
    
                // distance table
                for(i = 0; i < 30; i++)	// make an incomplete code set
                    l[i] = 5;
                zip_fixed_bd = 5;
    
                h = new zip_HuftBuild(l, 30, 0, zip_cpdist, zip_cpdext, zip_fixed_bd);
                if(h.status > 1) {
                    zip_fixed_tl = null;
                    alert("HufBuild error: "+h.status);
                    return -1;
                }
                zip_fixed_td = h.root;
                zip_fixed_bd = h.m;
            }
    
            zip_tl = zip_fixed_tl;
            zip_td = zip_fixed_td;
            zip_bl = zip_fixed_bl;
            zip_bd = zip_fixed_bd;
            return zip_inflate_codes(buff, off, size);
        }
    
        function zip_inflate_dynamic(buff, off, size) {
            // decompress an inflated type 2 (dynamic Huffman codes) block.
            var i;		// temporary variables
            var j;
            var l;		// last length
            var n;		// number of lengths to get
            var t;		// (zip_HuftNode) literal/length code table
            var nb;		// number of bit length codes
            var nl;		// number of literal/length codes
            var nd;		// number of distance codes
            var ll = new Array(286+30); // literal/length and distance code lengths
            var h;		// (zip_HuftBuild)
    
            for(i = 0; i < ll.length; i++)
                ll[i] = 0;
    
            // read in table lengths
            zip_NEEDBITS(5);
            nl = 257 + zip_GETBITS(5);	// number of literal/length codes
            zip_DUMPBITS(5);
            zip_NEEDBITS(5);
            nd = 1 + zip_GETBITS(5);	// number of distance codes
            zip_DUMPBITS(5);
            zip_NEEDBITS(4);
            nb = 4 + zip_GETBITS(4);	// number of bit length codes
            zip_DUMPBITS(4);
            if(nl > 286 || nd > 30)
                return -1;		// bad lengths
    
            // read in bit-length-code lengths
            for(j = 0; j < nb; j++)
            {
                zip_NEEDBITS(3);
                ll[zip_border[j]] = zip_GETBITS(3);
                zip_DUMPBITS(3);
            }
            for(; j < 19; j++)
                ll[zip_border[j]] = 0;
    
            // build decoding table for trees--single level, 7 bit lookup
            zip_bl = 7;
            h = new zip_HuftBuild(ll, 19, 19, null, null, zip_bl);
            if(h.status != 0)
                return -1;	// incomplete code set
    
            zip_tl = h.root;
            zip_bl = h.m;
    
            // read in literal and distance code lengths
            n = nl + nd;
            i = l = 0;
            while(i < n) {
                zip_NEEDBITS(zip_bl);
                t = zip_tl.list[zip_GETBITS(zip_bl)];
                j = t.b;
                zip_DUMPBITS(j);
                j = t.n;
                if(j < 16)		// length of code in bits (0..15)
                    ll[i++] = l = j;	// save last length in l
                else if(j == 16) {	// repeat last length 3 to 6 times
                    zip_NEEDBITS(2);
                    j = 3 + zip_GETBITS(2);
                    zip_DUMPBITS(2);
                    if(i + j > n)
                        return -1;
                    while(j-- > 0)
                        ll[i++] = l;
                } else if(j == 17) {	// 3 to 10 zero length codes
                    zip_NEEDBITS(3);
                    j = 3 + zip_GETBITS(3);
                    zip_DUMPBITS(3);
                    if(i + j > n)
                        return -1;
                    while(j-- > 0)
                        ll[i++] = 0;
                    l = 0;
                } else {		// j == 18: 11 to 138 zero length codes
                    zip_NEEDBITS(7);
                    j = 11 + zip_GETBITS(7);
                    zip_DUMPBITS(7);
                    if(i + j > n)
                        return -1;
                    while(j-- > 0)
                        ll[i++] = 0;
                    l = 0;
                }
            }
    
            // build the decoding tables for literal/length and distance codes
            zip_bl = zip_lbits;
            h = new zip_HuftBuild(ll, nl, 257, zip_cplens, zip_cplext, zip_bl);
            if(zip_bl == 0)	// no literals or lengths
                h.status = 1;
            if(h.status != 0) {
                if(h.status == 1)
                    ;// **incomplete literal tree**
                return -1;		// incomplete code set
            }
            zip_tl = h.root;
            zip_bl = h.m;
    
            for(i = 0; i < nd; i++)
                ll[i] = ll[i + nl];
            zip_bd = zip_dbits;
            h = new zip_HuftBuild(ll, nd, 0, zip_cpdist, zip_cpdext, zip_bd);
            zip_td = h.root;
            zip_bd = h.m;
    
            if(zip_bd == 0 && nl > 257) {   // lengths but no distances
                // **incomplete distance tree**
                return -1;
            }
    
            if(h.status == 1) {
                ;// **incomplete distance tree**
            }
            if(h.status != 0)
                return -1;
    
            // decompress until an end-of-block code
            return zip_inflate_codes(buff, off, size);
        }
    
        function zip_inflate_start() {
            var i;
    
            if(zip_slide == null)
                zip_slide = new Array(2 * zip_WSIZE);
            zip_wp = 0;
            zip_bit_buf = 0;
            zip_bit_len = 0;
            zip_method = -1;
            zip_eof = false;
            zip_copy_leng = zip_copy_dist = 0;
            zip_tl = null;
        }
    
        function zip_inflate_internal(buff, off, size) {
            // decompress an inflated entry
            var n, i;
    
            n = 0;
            while(n < size) {
                if(zip_eof && zip_method == -1)
                    return n;
    
                if(zip_copy_leng > 0) {
                    if(zip_method != zip_STORED_BLOCK) {
                        // STATIC_TREES or DYN_TREES
                        while(zip_copy_leng > 0 && n < size) {
                            zip_copy_leng--;
                            zip_copy_dist &= zip_WSIZE - 1;
                            zip_wp &= zip_WSIZE - 1;
                            buff[off + n++] = zip_slide[zip_wp++] =
                                zip_slide[zip_copy_dist++];
                        }
                    } else {
                        while(zip_copy_leng > 0 && n < size) {
                            zip_copy_leng--;
                            zip_wp &= zip_WSIZE - 1;
                            zip_NEEDBITS(8);
                            buff[off + n++] = zip_slide[zip_wp++] = zip_GETBITS(8);
                            zip_DUMPBITS(8);
                        }
                        if(zip_copy_leng == 0)
                            zip_method = -1; // done
                    }
                    if(n == size)
                        return n;
                }
    
                if(zip_method == -1) {
                    if(zip_eof)
                        break;
    
                    // read in last block bit
                    zip_NEEDBITS(1);
                    if(zip_GETBITS(1) != 0)
                        zip_eof = true;
                    zip_DUMPBITS(1);
    
                    // read in block type
                    zip_NEEDBITS(2);
                    zip_method = zip_GETBITS(2);
                    zip_DUMPBITS(2);
                    zip_tl = null;
                    zip_copy_leng = 0;
                }
    
                switch(zip_method) {
                case 0: // zip_STORED_BLOCK
                    i = zip_inflate_stored(buff, off + n, size - n);
                    break;
    
                case 1: // zip_STATIC_TREES
                    if(zip_tl != null)
                        i = zip_inflate_codes(buff, off + n, size - n);
                    else
                        i = zip_inflate_fixed(buff, off + n, size - n);
                    break;
    
                case 2: // zip_DYN_TREES
                    if(zip_tl != null)
                        i = zip_inflate_codes(buff, off + n, size - n);
                    else
                        i = zip_inflate_dynamic(buff, off + n, size - n);
                    break;
    
                default: // error
                    i = -1;
                    break;
                }
    
                if(i == -1) {
                    if(zip_eof)
                        return 0;
                    return -1;
                }
                n += i;
            }
            return n;
        }
    
    
        var JSInflate = {};
        GLOBAL.JSInflate = JSInflate;
    
        JSInflate.inflate = function (data, raw) {
            var out, buff;
            var i, j;
    
            zip_inflate_start();
            zip_inflate_data = data;
            zip_inflate_pos = 0;
    
            buff = new Array(1024);
            out = [];
            while((i = zip_inflate_internal(buff, 0, buff.length)) > 0) {
                for(j = 0; j < i; j++)
                    out.push(raw ? buff[j] : String.fromCharCode(buff[j]));
            }
            zip_inflate_data = null; // G.C.
    
            return raw ? out : out.join('');
        };
    }(this));
    var win = window,
        doc = win.document,
        fromCharCode = String.fromCharCode,
        push = Array.prototype.push,
        min = Math.min,
        max = Math.max;
    
    Gordon = {
        debug: false,
        qualityValues: {
            LOW: "low",
            AUTO_LOW: "autolow",
            AUTO_HIGH: "autohigh",
            MEDIUM: "medium",
            HIGH: "high",
            BEST: "best"
        },
        scaleValues: {
            SHOW_ALL: "showall",
            NO_ORDER: "noorder",
            EXACT_FIT: "exactfit"
        },
        validSignatures: {
            SWF: "FWS",
            COMPRESSED_SWF: "CWS"
        },
        readyStates: {
            LOADING: 0,
            UNINITIALIZED: 1,
            LOADED: 2,
            INTERACTIVE: 3,
            COMPLETE: 4
        },
        tagCodes: {
            END: 0,
            SHOW_FRAME: 1,
            DEFINE_SHAPE: 2,
            PLACE_OBJECT: 4,
            REMOVE_OBJECT: 5,
            DEFINE_BITS: 6,
            DEFINE_BUTTON: 7,
            JPEG_TABLES: 8,
            SET_BACKGROUND_COLOR: 9,
            DEFINE_FONT: 10,
            DEFINE_TEXT: 11,
            DO_ACTION: 12,
            DEFINE_FONT_INFO: 13,
            DEFINE_SOUND: 14,
            START_SOUND: 15,
            DEFINE_BUTTON_SOUND: 17,
            SOUND_STREAM_HEAD: 18,
            SOUND_STREAM_BLOCK: 19,
            DEFINE_BITS_LOSSLESS: 20,
            DEFINE_BITS_JPEG2: 21,
            DEFINE_SHAPE2: 22,
            DEFINE_BUTTON_CXFORM: 23,
            PROTECT: 24,
            PLACE_OBJECT2: 26,
            REMOVE_OBJECT2: 28,
            DEFINE_SHAPE3: 32,
            DEFINE_TEXT2: 33,
            DEFINE_BUTTON2: 34,
            DEFINE_BITS_JPEG3: 35,
            DEFINE_BITS_LOSSLESS2: 36,
            DEFINE_EDIT_TEXT: 37,
            DEFINE_SPRITE: 39,
            FRAME_LABEL: 43,
            SOUND_STREAM_HEAD2: 45,
            DEFINE_MORPH_SHAPE: 46,
            DEFINE_FONT2: 48,
            EXPORT_ASSETS: 56,
            IMPORT_ASSETS: 57,
            ENABLE_DEBUGGER: 58,
            DO_INIT_ACTION: 59,
            DEFINE_VIDEO_STREAM: 60,
            VIDEO_FRAME: 61,
            DEFINE_FONT_INFO2: 62,
            ENABLE_DEBUGGER2: 64,
            SCRIPT_LIMITS: 65,
            SET_TAB_INDEX: 66,
            FILE_ATTRIBUTES: 69,
            PLACE_OBJECT3: 70,
            IMPORT_ASSETS2: 71,
            DEFINE_FONT_ALIGN_ZONES: 73,
            CSM_TEXT_SETTINGS: 74,
            DEFINE_FONT3: 75,
            SYMBOL_CLASS: 76,
            METADATA: 77,
            DEFINE_SCALING_GRID: 78,
            DO_ABC: 82,
            DEFINE_SHAPE4: 83,
            DEFINE_MORPH_SHAPE2: 84,
            DEFINE_SCENE_AND_FRAME_LABEL_DATA: 86,
            DEFINE_BINARY_DATA: 87,
            DEFINE_FONT_NAME: 88,
            START_SOUND2: 89,
            DEFINE_BITS_JPEG4: 90,
            DEFINE_FONT4: 91
        },
        controlTags: [0, 1, 4, 5, 15, 18, 19, 26, 28, 43, 45],
        tagNames: {},
        tagHandlers: {},
        fillStyleTypes: {
            SOLID: 0x00, 
            LINEAR_GRADIENT: 0x10, 
            RADIAL_GRADIENT: 0x12,
            FOCAL_RADIAL_GRADIENT: 0x13,
            REPEATING_BITMAP: 0x40, 
            CLIPPED_BITMAP: 0x41, 
            NON_SMOOTHED_REPEATING_BITMAP: 0x42,
            NON_SMOOTHED_CLIPPED_BITMAP: 0x43
        },
        spreadModes: {
            PAD: 0,
            REFLECT: 1,
            REPEAT: 2
        },
        interpolationModes: {
            RGB: 0,
            LINEAR_RGB: 1
        },
        styleChangeStates: {
            MOVE_TO: 0x01,
            LEFT_FILL_STYLE: 0x02,
            RIGHT_FILL_STYLE: 0x04,
            LINE_STYLE: 0x08,
            NEW_STYLES: 0x10
        },
        buttonStates: {
            UP: 0x01,
            OVER: 0x02,
            DOWN: 0x04,
            HIT: 0x08
        },
        mouseButtons: {
            LEFT: 1,
            RIGHT: 2,
            MIDDLE: 3
        },
        textStyleFlags: {
            HAS_FONT: 0x08,
            HAS_COLOR: 0x04,
            HAS_XOFFSET: 0x01,
            HAS_YOFFSET: 0x02
        },
        actionCodes: {
            NEXT_FRAME: 0x04,
            PREVIOUS_FRAME: 0x05,
            PLAY: 0x06,
            STOP: 0x07,
            TOGGLE_QUALITY: 0x08,
            STOP_SOUNDS: 0x09,
            ADD: 0x0a,
            SUBTRACT: 0x0b,
            MULTIPLY: 0x0c,
            DIVIDE: 0x0d,
            EQUALS: 0x0e,
            LESS: 0x0f,
            AND: 0x10,
            OR: 0x11,
            NOT: 0x12,
            STRING_EQUALS: 0x13,
            STRING_LENGTH: 0x14,
            STRING_EXTRACT: 0x15,
            POP: 0x17,
            TO_INTEGER: 0x18,
            GET_VARIABLE: 0x1c,
            SET_VARIABLE: 0x1d,
            SET_TARGET2: 0x20,
            STRING_ADD: 0x21,
            GET_PROPERTY: 0x22,
            SET_PROPERTY: 0x23,
            CLONE_SPRITE: 0x24,
            REMOVE_SPRITE: 0x25,
            TRACE: 0x26,
            START_DRAG: 0x27,
            END_DRAG: 0x28,
            STRING_LESS: 0x29,
            THROW: 0x2a,
            CAST_OP: 0x2b,
            IMPLEMENTS_OP: 0x2c,
            FS_COMMAND2: 0x2d,
            RANDOM_NUMBER: 0x30,
            MBSTRING_LENGTH: 0x31,
            CHAR_TO_ASCII: 0x32,
            ASCII_TO_CHAR: 0x33,
            GET_TIME: 0x34,
            MBSTRING_EXTRACT: 0x35,
            MBCHAR_TO_ASCII: 0x36,
            MBASCII_TO_CHAR: 0x37,
            DELETE: 0x3a,
            DELETE2: 0x3b,
            DEFINE_LOCAL: 0x3c,
            CALL_FUNCTION: 0x3d,
            RETURN: 0x3e,
            MODULO: 0x3f,
            NEW_OBJECT: 0x40,
            DEFINE_LOCAL2: 0x41,
            INIT_ARRAY: 0x42,
            INIT_OBJECT: 0x43,
            TYPE_OF: 0x44,
            TARGET_PATH: 0x45,
            ENUMERATE: 0x46,
            ADD2: 0x47,
            LESS2: 0x48,
            EQUALS2: 0x49,
            TO_NUMBER: 0x4a,
            TO_STRING: 0x4b,
            PUSH_DUPLICATE: 0x4c,
            STACK_SWAP: 0x4d,
            GET_MEMBER: 0x4e,
            SET_MEMBER: 0x4f,
            INCREMENT: 0x50,
            DECREMENT: 0x51,
            CALL_METHOD: 0x52,
            NEW_METHOD: 0x53,
            INSTANCE_OF: 0x54,
            ENUMERATE2: 0x55,
            DO_INIT_ACTION: 0x59,
            BIT_AND: 0x60,
            BIT_OR: 0x61,
            BIT_XOR: 0x62,
            BIT_LSHIFT: 0x63,
            BIT_RSHIFT: 0x64,
            BIT_URSHIFT: 0x65,
            STRICT_EQUALS: 0x66,
            GREATER: 0x67,
            STRING_GREATER: 0x68,
            EXTENDS: 0x69,
            GOTO_FRAME: 0x81,
            DO_ABC: 0x82,
            GET_URL: 0x83,
            STORE_REGISTER: 0x87,
            CONSTANT_POOL: 0x88,
            WAIT_FOR_FRAME: 0x8a,
            SET_TARGET: 0x8b,
            SET_GO_TO_LABEL: 0x8c,
            WAIT_FOR_FRAME2: 0x8d,
            DEFINE_FUNCTION2: 0x8e,
            TRY: 0x8f,
            WITH: 0x94,
            PUSH: 0x96,
            JUMP: 0x99,
            GET_URL2: 0x9a,
            DEFINE_FUNCTION: 0x9b,
            IF: 0x9d,
            CALL: 0x9e,
            GOTO_FRAME2: 0x9f
        },
        valueTypes: {
            STRING: 0,
            FLOATING_POINT: 1,
            NULL: 2,
            UNDEFINED: 3,
            REGISTER: 4,
            BOOLEAN: 5,
            DOUBLE: 6,
            INTEGER: 7,
            CONSTANT8: 8,
            SWIFF_CONSTANT16: 9
        },
        urlTargets: {
            SELF: "_self",
            BLANK: "_blank",
            PARENT: "_parent",
            TOP: "_top"
        },
        bitmapFormats: {
            COLORMAPPED: 3,
            RGB15: 4,
            RGB24: 5
        },
        placeFlags: {
            MOVE: 0x01,
            HAS_CHARACTER: 0x02,
            HAS_MATRIX: 0x04,
            HAS_CXFORM: 0x08,
            HAS_RATIO: 0x10,
            HAS_NAME: 0x20,
            HAS_CLIP_DEPTH: 0x40,
            HAS_CLIP_ACTIONS: 0x80
        },
        placeFlags2: {
        	HAS_IMAGE: 0x10,
        	HAS_CLASS_NAME: 0x08,
        	HAS_CACHE_AS_BITMAP: 0x04,
        	HAS_BLEND_MODE: 0x02,
        	HAS_FILTER_LIST: 0x01
        },
        filters: [
            'DropShadowFilter',
            'BlurFilter',
            'GlowFilter',
            'BevelFilter',
            'GradientGlowFilter',
            'ConvolutionFilter',
            'ColorMatrixFilter',
            'GradientBevelFilter'
    	],
        defaultRenderer: null
    };
    
    (function(){
        var t = Gordon.tagCodes,
            n = Gordon.tagNames,
            h = Gordon.tagHandlers;
        for(var name in t){
            var code = t[name];
            n[code] = name;
            h[code] = "_handle" + name.toLowerCase().replace(/(^|_)([a-z])/g, function(match, p1, p2){
                return p2.toUpperCase();
            });
        }
    })();
    
    var console = window.console || {
        log: function(){}
    }
    
    function trace(){
        if(Gordon.debug){ console.log.apply(console, arguments); }
    }
    
    (function(){
        var DEFLATE_CODE_LENGTH_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15],
            DEFLATE_CODE_LENGHT_MAP = [
                [0, 3], [0, 4], [0, 5], [0, 6], [0, 7], [0, 8], [0, 9], [0, 10], [1, 11], [1, 13], [1, 15], [1, 17],
                [2, 19], [2, 23], [2, 27], [2, 31], [3, 35], [3, 43], [3, 51], [3, 59], [4, 67], [4, 83], [4, 99],
                [4, 115], [5, 131], [5, 163], [5, 195], [5, 227], [0, 258]
            ],
            DEFLATE_DISTANCE_MAP = [
                [0, 1], [0, 2], [0, 3], [0, 4], [1, 5], [1, 7], [2, 9], [2, 13], [3, 17], [3, 25], [4, 33], [4, 49],
                [5, 65], [5, 97], [6, 129], [6, 193], [7, 257], [7, 385], [8, 513], [8, 769], [9, 1025], [9, 1537],
                [10, 2049], [10, 3073], [11, 4097], [11, 6145], [12, 8193], [12, 12289], [13, 16385], [13, 24577]
            ];
        
        Gordon.Stream = function(data){
            var buff = [],
                t = this,
                i = t.length = data.length;
            t.offset = 0;
            for(var i = 0; data[i]; i++){ buff.push(fromCharCode(data.charCodeAt(i) & 0xff)); }
            t._buffer = buff.join('');
            t._bitBuffer = null;
            t._bitOffset = 8;
        };
        Gordon.Stream.prototype = {
            readByteAt: function(pos){
                return this._buffer.charCodeAt(pos);
            },
            
            readNumber: function(numBytes, bigEnd){
                var t = this,
                    val = 0;
                if(bigEnd){
                    while(numBytes--){ val = (val << 8) | t.readByteAt(t.offset++); }
                }else{
                    var o = t.offset,
                        i = o + numBytes;
                    while(i > o){ val = (val << 8) | t.readByteAt(--i); }
                    t.offset += numBytes;
                }
                t.align();
                return val;
            },
            
            readSNumber: function(numBytes, bigEnd){
                var val = this.readNumber(numBytes, bigEnd),
                    numBits = numBytes * 8;
                if(val >> (numBits - 1)){ val -= Math.pow(2, numBits); }
                return val;
            },
            
            readSI8: function(){
                return this.readSNumber(1);
            },
            
            readSI16: function(bigEnd){
                return this.readSNumber(2, bigEnd);
            },
            
            readSI32: function(bigEnd){
                return this.readSNumber(4, bigEnd);
            },
            
            readUI8: function(){
                return this.readNumber(1);
            },
            
            readUI16: function(bigEnd){
                return this.readNumber(2, bigEnd);
            },
            
            readUI24: function(bigEnd){
                return this.readNumber(3, bigEnd);
            },
            
            readUI32: function(bigEnd){
                return this.readNumber(4, bigEnd);
            },
            
            readFixed: function(){
                return this._readFixedPoint(32, 16);
            },
            
            _readFixedPoint: function(numBits, precision){
                return this.readSB(numBits) * Math.pow(2, -precision);
            },
            
            readFixed8: function(){
                return this._readFixedPoint(16, 8);
            },
            
            readFloat: function(){
                return this._readFloatingPoint(8, 23);
            },
            
            _readFloatingPoint: function(numEBits, numSBits){
                var numBits = 1 + numEBits + numSBits,
                    numBytes = numBits / 8,
                    t = this,
                    val = 0.0;
                if(numBytes > 4){
                    var i = Math.ceil(numBytes / 4);
                    while(i--){
                        var buff = [],
                            o = t.offset,
                            j = o + (numBytes >= 4 ? 4 : numBytes % 4);
                        while(j > o){
                            buff.push(t.readByteAt(--j));
                            numBytes--;
                            t.offset++;
                        }
                    }
                    var s = new Gordon.Stream(fromCharCode.apply(String, buff)),
                        sign = s.readUB(1),
                        expo = s.readUB(numEBits),
                        mantis = 0,
                        i = numSBits;
                    while(i--){
                        if(s.readBool()){ mantis += Math.pow(2, i); }
                    }
                }else{
                    var sign = t.readUB(1),
                        expo = t.readUB(numEBits),
                        mantis = t.readUB(numSBits);
                }
                if(sign || expo || mantis){
                    var maxExpo = Math.pow(2, numEBits),
                        bias = ~~((maxExpo - 1) / 2),
                        scale = Math.pow(2, numSBits),
                        fract = mantis / scale;
                    if(bias){
                        if(bias < maxExpo){ val = Math.pow(2, expo - bias) * (1 + fract); }
                        else if(fract){ val = NaN; }
                        else{ val = Infinity; }
                    }else if(fract){ val = Math.pow(2, 1 - bias) * fract; }
                    if(NaN != val && sign){ val *= -1; }
                }
                return val;
            },
            
            readFloat16: function(){
                return this._readFloatingPoint(5, 10);
            },
            
            readDouble: function(){
                return this._readFloatingPoint(11, 52);
            },
            
            readEncodedU32: function(){
                var val = 0;
                for(var i = 0; i < 5; i++){
                    var num = this.readByteAt(this._offset++);
                    val = val | ((num & 0x7f) << (7 * i));
                    if(!(num & 0x80)){ break; }
                }
                return val;
            },
            
            readSB: function(numBits){
                var val = this.readUB(numBits);
                if(val >> (numBits - 1)){ val -= Math.pow(2, numBits); }
                return val;
            },
            
            readUB: function(numBits, lsb){
                var t = this,
                    val = 0;
                for(var i = 0; i < numBits; i++){
                    if(8 == t._bitOffset){
                        t._bitBuffer = t.readUI8();
                        t._bitOffset = 0;
                    }
                    if(lsb){ val |= (t._bitBuffer & (0x01 << t._bitOffset++) ? 1 : 0) << i; }
                    else{ val = (val << 1) | (t._bitBuffer & (0x80 >> t._bitOffset++) ? 1 : 0); }
                }
                return val;
            },
            
            readFB: function(numBits){
                return this._readFixedPoint(numBits, 16);
            },
            
            readString: function(numChars){
                var t = this,
                    b = t._buffer;
                if(undefined != numChars){
                    var str = b.substr(t.offset, numChars);
                    t.offset += numChars;
                }else{
                    var chars = [],
                        i = t.length - t.offset;
                    while(i--){
                        var code = t.readByteAt(t.offset++);
                        if(code){ chars.push(fromCharCode(code)); }
                        else{ break; }
                    }
                    var str = chars.join('');
                }
                return str;
            },
            
            readBool: function(numBits){
                return !!this.readUB(numBits || 1);
            },
            
            seek: function(offset, absolute){
                var t = this;
                t.offset = (absolute ? 0 : t.offset) + offset;
                t.align();
                return t;
            },
            
            align: function(){
                this._bitBuffer = null;
                this._bitOffset = 8;
                return this;
            },
            
            readLanguageCode: function(){
                return this.readUI8();
            },
            
            readRGB: function(){
                return {
                    red: this.readUI8(),
                    green: this.readUI8(),
                    blue: this.readUI8()
                };
            },
            
            readRGBA: function(){
                var rgba = this.readRGB();
                rgba.alpha = this.readUI8();
                return rgba;
            },
            
            readARGB: function(){
                var alpha = this.readUI8(),
                    rgba = this.readRGB();
                rgba.alpha = alpha;
                return rgba;
            },
            
            readRect: function(){
                var t = this;
                    numBits = t.readUB(5),
                    rect = {
                        left: t.readSB(numBits),
                        right: t.readSB(numBits),
                        top: t.readSB(numBits),
                        bottom: t.readSB(numBits)
                    };
                t.align();
                return rect;
            },
            
            readMatrix: function(){
                var t = this,
                    hasScale = t.readBool();
                if(hasScale){
                    var numBits = t.readUB(5),
                        scaleX = t.readFB(numBits),
                        scaleY = t.readFB(numBits);
                }else{ var scaleX = scaleY = 1.0; }
                var hasRotation = t.readBool();
                if(hasRotation){
                    var numBits = t.readUB(5),
                        skewX = t.readFB(numBits),
                        skewY = t.readFB(numBits);
                }else{ var skewX =  skewY = 0.0; }
                var numBits = t.readUB(5);
                    matrix = {
                        scaleX: scaleX, scaleY: scaleY,
                        skewX: skewX, skewY: skewY,
                        moveX: t.readSB(numBits), moveY: t.readSB(numBits)
                    };
                t.align();
                return matrix;
            },
            
            readCxform: function(){
                return this._readCxf();
            },
            
            readCxformA: function(){
                return this._readCxf(true);
            },
            
            _readCxf: function(withAlpha){
                var t = this;
                    hasAddTerms = t.readBool(),
                    hasMultTerms = t.readBool(),
                    numBits = t.readUB(4);
                if(hasMultTerms){
                    var multR = t.readSB(numBits) / 256,
                        multG = t.readSB(numBits) / 256,
                        multB = t.readSB(numBits) / 256,
                        multA = withAlpha ? t.readSB(numBits) / 256 : 1;
                }else{ var multR = multG = multB = multA = 1; }
                if(hasAddTerms){
                    var addR = t.readSB(numBits),
                        addG = t.readSB(numBits),
                        addB = t.readSB(numBits),
                        addA = withAlpha ? t.readSB(numBits) / 256 : 0;
                }else{ var addR = addG = addB = addA = 0; }
                var cxform = {
                    multR: multR, multG: multG, multB: multB, multA: multA,
                    addR: addR, addG: addG, addB: addB, addA: addA
                }
                t.align();
                return cxform;
            },
            
            decompress: function(){
                var t = this,
                    b = t._buffer,
                    o = t.offset,
                    data = b.substr(0, o) + t.unzip(false);
                t.length = data.length;
                t.offset = o;
                t._buffer = data;
                return t;
            },
            
            unzip: function(raw) {
                var t = this,
    	            b = t._buffer,
    	            o = t.offset,
    	            data = JSInflate.inflate(b.substring(o + 2), raw);
            	return data;
            }
        };
    })();
    
    (function(){
    	var USE_WEB_WORKER = true;
    	
        if(USE_WEB_WORKER && doc && window.Worker){
            var REGEXP_SCRIPT_SRC = /(^|.*\/)gordon.(min\.)?js$/,
                scripts = doc.getElementsByTagName("script"),
                src = '',
                i = scripts.length;
            while(i--){
                var path = scripts[i].src;
                if(REGEXP_SCRIPT_SRC.test(path)){
                    src = path;
                    break;
                }
            }
            worker = new Worker(src);
            
            Gordon.Parser = function(data, ondata){
                var t = this,
                    w = t._worker = worker;
                t.data = data;
                t.ondata = ondata;
                
                w.onmessage = function(e){
                    t.ondata(e.data);
                };
                
                w.postMessage(data);
            };
        }else{
            Gordon.Parser = function(url, ondata){
                var xhr = new XMLHttpRequest(),
                    t = this;
                xhr.open("GET", url, false);
                xhr.overrideMimeType("text/plain; charset=x-user-defined");
                xhr.send();
                if(200 != xhr.status && 0 != xhr.status){ throw new Error("Unable to load " + url + " status: " + xhr.status); }
                if(ondata) { t.ondata = ondata; }
                var s = t._stream = new Gordon.Stream(xhr.responseText),
                    sign = s.readString(3),
                    v = Gordon.validSignatures,
                    version = s.readUI8(),
                    fileLen = s.readUI32(),
                    h = Gordon.tagHandlers,
                    f = Gordon.tagCodes.SHOW_FRAME;
                if(sign == v.COMPRESSED_SWF){ s.decompress(); }
                else if(sign != v.SWF){ throw new Error(url + " is not a SWF movie file"); }
                this.ondata({
                    type: "header",
                    version: version,
                    fileLength: fileLen,
                    frameSize: s.readRect(),
                    frameRate: s.readUI16() / 256,
                    frameCount: s.readUI16()
                });
    //            console.info('ver: '+version);
                t._dictionary = {};
                t._jpegTables = null;
                var startTime = Date.now();
                do{
                    var frm = {
                        type: "frame",
                        displayList: {}
                    };
                    do{
                        var hdr = s.readUI16(),
                            code = hdr >> 6,
                            len = hdr & 0x3f,
                            handl = h[code];
                        if(0x3f == len){ len = s.readUI32(); }
                        var offset = s.offset;
                        if(code){
    /*
                        	var tagName = (Gordon.tagNames[code] || code.toString(16)),
                        		id = '';
                        	if(tagName.substring(0, 6) == 'DEFINE') {
                        		id = s.readUI16();
                        		s.seek(-2);
                        	}
                        	console.info(tagName+':'+id+':'+len);
    */
                        	
                            if(code == f){
                                t.ondata(frm);
                                break;
                            }
                            if(t[handl]){ t[handl](s, offset, len, frm); }
                            else{
    //                        	console.warn('skipped');
                            	s.seek(len);
                            }
                        }
                    }while(code && code != f);
                }while(code);
                var endTime = Date.now();
                t.ondata({'type': 'debug', 'msg': (endTime - startTime), 'id': -1});
            };
            Gordon.Parser.prototype = {
                ondata: function(data){
                    postMessage(data);
                },
                
                _handleDefineShape: function(s, offset, len, frm, withAlpha){
                    var id = s.readUI16(),
                        shape = {
                            type: "shape",
                            id: id,
                            bounds: s.readRect()
                        },
                        t = this,
                        fillStyles = t._readFillStyles(s, withAlpha),
                        lineStyles = t._readLineStyles(s, withAlpha),
                        edges = t._readEdges(s, fillStyles, lineStyles, withAlpha);
                    if(edges instanceof Array){
                        var segments = shape.segments = [];
                        for(var i = 0, seg = edges[0]; seg; seg = edges[++i]){ segments.push({
                            type: "shape",
                            id: id + '-' + (i + 1),
                            commands: edges2cmds(seg.records, !!seg.line),
                            records: seg.records,
                            fill: seg.fill,
                            line: seg.line
                        }); }
                    }else{
                        shape.commands = edges2cmds(edges.records, !!edges.line),
                        shape.records = edges.records,
                        shape.fill = edges.fill,
                        shape.line = edges.line;
                    }
                    t.ondata(shape);
                    t._dictionary[id] = shape;
                    return t;
                },
                
                _readEdges: function(s, fillStyles, lineStyles, withAlpha, morph){
                    var t = this,
                    	numFillBits = s.readUB(4),
                        numLineBits = s.readUB(4),
                        x1 = 0,
                        y1 = 0,
                        x2 = 0,
                        y2 = 0,
                        seg = [],
                        i = 0,
                        isFirst = true,
                        edges = [],
                        leftFill = 0,
                        rightFill = 0,
                        fsOffset = 0,
                        lsOffset = 0,
                        leftFillEdges = {},
                        rightFillEdges = {},
                        line = 0,
                        lineEdges = {},
                        c = Gordon.styleChangeStates,
                        countFChanges = 0,
                        countLChanges = 0,
                        useSinglePath = true;
                    do{
                        var type = s.readUB(1),
                            flags = null;
                        if(type){
                            var isStraight = s.readBool(),
                                numBits = s.readUB(4) + 2,
                                cx = null,
                                cy = null;
                            x1 = x2;
                            y1 = y2;
                            if(isStraight){
                                var isGeneral = s.readBool();
                                if(isGeneral){
                                    x2 += s.readSB(numBits);
                                    y2 += s.readSB(numBits);
                                }else{
                                    var isVertical = s.readBool();
                                        if(isVertical){ y2 += s.readSB(numBits); }
                                        else{ x2 += s.readSB(numBits); }
                                    }
                            }else{
                                cx = x1 + s.readSB(numBits);
                                cy = y1 + s.readSB(numBits);
                                x2 = cx + s.readSB(numBits);
                                y2 = cy + s.readSB(numBits);
                            }
                            seg.push({
                                i: i++,
                                f: isFirst,
                                x1: x1, y1: y1,
                                cx: cx, cy: cy,
                                x2: x2, y2: y2
                            });
                            isFirst = false;
                        }else{
                            if(seg.length){
                                push.apply(edges, seg);
                                if(leftFill){
                                    var idx = fsOffset + leftFill,
                                        list = leftFillEdges[idx] || (leftFillEdges[idx] = []);
                                    for(var j = 0, edge = seg[0]; edge; edge = seg[++j]){
                                        var e = cloneEdge(edge),
                                            tx1 = e.x1,
                                            ty1 = e.y1;
                                        e.i = i++;
                                        e.x1 = e.x2;
                                        e.y1 = e.y2;
                                        e.x2 = tx1;
                                        e.y2 = ty1;
                                        list.push(e);
                                    }
                                }
                                if(rightFill){
                                    var idx = fsOffset + rightFill,
                                        list = rightFillEdges[idx] || (rightFillEdges[idx] = []);
                                    push.apply(list, seg);
                                }
                                if(line){
                                    var idx = lsOffset + line,
                                        list = lineEdges[idx] || (lineEdges[idx] = []);
                                    push.apply(list, seg);
                                }
                                seg = [];
                                isFirst = true;
                            }
                            var flags = s.readUB(5);
                            if(flags){
                                if(flags & c.MOVE_TO){
                                    var numBits = s.readUB(5);
                                    x2 = s.readSB(numBits);
                                    y2 = s.readSB(numBits);
                                }
                                if(flags & c.LEFT_FILL_STYLE){
                                    leftFill = s.readUB(numFillBits);
                                    countFChanges++;
                                }
                                if(flags & c.RIGHT_FILL_STYLE){
                                    rightFill = s.readUB(numFillBits);
                                    countFChanges++;
                                }
                                if(flags & c.LINE_STYLE){
                                    line = s.readUB(numLineBits);
                                    countLChanges++;
                                }
                                if((leftFill && rightFill) || countFChanges + countLChanges > 2){ useSinglePath = false; }
                                if(flags & c.NEW_STYLES){
                                    fsOffset = fillStyles.length;
                                    lsOffset = lineStyles.length;
                                    push.apply(fillStyles, t._readFillStyles(s, withAlpha, morph));
                                    push.apply(lineStyles, t._readLineStyles(s, withAlpha, morph));
                                    numFillBits = s.readUB(4);
                                    numLineBits = s.readUB(4);
                                    useSinglePath = false;
                                }
                            }
                        }
                    }while(type || flags);
                    s.align();
                    if(useSinglePath){
                        var fill = leftFill || rightFill;
                        return {
                            records: edges,
                            fill: fill ? fillStyles[fsOffset + fill - 1] : null,
                            line: lineStyles[lsOffset + line - 1]
                        };
                    }else{
                        var segments = [];
                        for(var i = 0; fillStyles[i]; i++){
                            var fill = i + 1,
                                list = leftFillEdges[fill],
                                fillEdges = [],
                                edgeMap = {};
                            if(list){ push.apply(fillEdges, list); }
                            list = rightFillEdges[fill];
                            if(list){ push.apply(fillEdges, list); }
                            for(var j = 0, edge = fillEdges[0]; edge; edge = fillEdges[++j]){
                                var key = pt2key(edge.x1, edge.y1),
                                    list = edgeMap[key] || (edgeMap[key] = []);
                                list.push(edge);
                            }
                            var recs = [],
                                countFillEdges = fillEdges.length,
                                l = countFillEdges - 1;
                            for(var j = 0; j < countFillEdges && !recs[l]; j++){
                                var edge = fillEdges[j];
                                if(!edge.c){
                                    var seg = [],
                                        firstKey = pt2key(edge.x1, edge.y1),
                                        usedMap = {};
                                    do{
                                        seg.push(edge);
                                        usedMap[edge.i] = true;
                                        var key = pt2key(edge.x2, edge.y2),
                                            list = edgeMap[key],
                                            favEdge = fillEdges[j + 1],
                                            nextEdge = null;
                                        if(key == firstKey){
                                            var k = seg.length;
                                            while(k--){ seg[k].c = true; }
                                            push.apply(recs, seg);
                                            break;
                                        }
                                        if (!(list && list.length)){ break; }
                                        for(var k = 0; list[k]; k++){
                                            var entry = list[k];
                                            if(entry == favEdge && !entry.c){
                                                list.splice(k, 1);
                                                nextEdge = entry;
                                            }
                                        }
                                        if(!nextEdge){
                                            for(var k = 0; list[k]; k++){
                                                var entry = list[k];
                                                if(!(entry.c || usedMap[entry.i])){ nextEdge = entry; }
                                            }
                                        }
                                        edge = nextEdge;
                                    }while(edge);
                                }
                            }
                            var l = recs.length;
                            if(l){ segments.push({
                                records: recs,
                                fill: fillStyles[i],
                                "_index": recs[l - 1].i
                            }); }
                        }
                        var i = lineStyles.length;
                        while(i--){
                            var recs = lineEdges[i + 1];
                            if(recs){ segments.push({
                                records: recs,
                                line: lineStyles[i],
                                _index: recs[recs.length - 1].i
                            }); }
                        }
                        segments.sort(function(a, b){
                            return a._index - b._index;
                        });
                        if(segments.length > 1){ return segments; }
                        else{ return segments[0]; }
                    }
                },
                
                _readFillStyles: function(s, withAlpha, morph){
                    var numStyles = s.readUI8(),
                        styles = [];
                    if(0xff == numStyles){ numStyles = s.readUI16(); }
                    while(numStyles--){
                        var type = s.readUI8(),
                            f = Gordon.fillStyleTypes;
                        switch(type){
                            case f.SOLID:
                                if(morph){ styles.push([s.readRGBA(), s.readRGBA()]); }
                                else{ styles.push(withAlpha ? s.readRGBA() : s.readRGB()); }
                                break;
                            case f.LINEAR_GRADIENT:
                            case f.RADIAL_GRADIENT:
                                if(morph){ var matrix = [nlizeMatrix(s.readMatrix()), nlizeMatrix(s.readMatrix())]; }
                                else{ var matrix = nlizeMatrix(s.readMatrix()); }
                                var stops = [],
                                    style = {
                                        type: type == f.LINEAR_GRADIENT ? "linear" : "radial",
                                        matrix: matrix,
                                        spread: morph ? Gordon.spreadModes.PAD : s.readUB(2),
                                        interpolation: morph ? Gordon.interpolationModes.RGB : s.readUB(2),
                                        stops: stops
                                    },
                                    numStops = s.readUB(4);
                                while(numStops--){
                                    var offset = s.readUI8() / 256,
                                        color = withAlpha || morph ? s.readRGBA() : s.readRGB();
                                    stops.push({
                                        offset: morph ? [offset, s.readUI8() / 256] : offset,
                                        color: morph ? [color, s.readRGBA()] : color
                                    });
                                }
                                styles.push(style);
                                break;
                            case f.REPEATING_BITMAP:
                            case f.CLIPPED_BITMAP:
                            case f.NON_SMOOTHED_REPEATING_BITMAP: /* Ghostoy: non-smoothed bitmap fill */
                            case f.NON_SMOOTHED_CLIPPED_BITMAP:
                                var imgId = s.readUI16(),
                                    img = this._dictionary[imgId],
                                    matrix = morph ? [s.readMatrix(), s.readMatrix()] : s.readMatrix();
                                if(img){
                                    styles.push({
                                        type: "pattern",
                                        image: img,
                                        matrix: matrix,
                                        repeat: type == f.REPEATING_BITMAP || type == f.NON_SMOOTHED_REPEATING_BITMAP
                                    });
                                }else{ styles.push(null); }
                                break;
                        }
                    }
                    return styles;
                },
                
                _readLineStyles: function(s, withAlpha, morph){
                    var numStyles = s.readUI8(),
                        styles = [];
                    if(0xff == numStyles){ numStyles = s.readUI16(); }
                    while(numStyles--){
                        var width = s.readUI16(),
                            color = withAlpha || morph ? s.readRGBA() : s.readRGB();
                        styles.push({
                            width: morph ? [width, s.readUI16()] : width,
                            color: morph ? [color, s.readRGBA()] : color
                        });
                    }
                    return styles;
                },
                
                _handlePlaceObject: function(s, offset, len, frm){
                    var objId = s.readUI16(),
                        depth = s.readUI16(),
                        t = this,
                        character = {
                            object: t._dictionary[objId].id,
                            depth: depth,
                            matrix: s.readMatrix()
                        };
                    if(s.offset - offset != len){ character.cxform = s.readCxform(); }
                    frm.displayList[depth] = character;
                    return t;
                },
                
                _handleRemoveObject: function(s, offset, len, frm){
                    var id = s.readUI16(),
                        depth = s.readUI16();
                    frm.displayList[depth] = null;
                    return this;
                },
                
                _handleDefineBits: function(s, offset, len, frm, withAlpha){
                    var id = s.readUI16(),
                        img = {
                            type: "image",
                            id: id,
                            width: 0,
                            height: 0
                        },
                        t = this,
                        h = t._jpegTables;
                    if(withAlpha){
                        var alphaDataOffset = s.readUI32(),
                            data = s.readString(alphaDataOffset);
                        img.alphaData = s.readString(len - (s.offset - offset));
                    }else{ var data = s.readString(len - 2); }
                    for(var i = 0; data[i]; i++){
                        var word = ((data.charCodeAt(i) & 0xff) << 8) | (data.charCodeAt(++i) & 0xff);
                        if(0xffd9 == word){
                            word = ((data.charCodeAt(++i) & 0xff) << 8) | (data.charCodeAt(++i) & 0xff);
                            if(word == 0xffd8){
                                i++;
                                data = data.substr(0, i - 4) + data.substr(i);
                                i -= 4;
                            }
                        }else if(0xffc0 == word){
                            i += 3;
                            img.height = ((data.charCodeAt(++i) & 0xff) << 8) | (data.charCodeAt(++i) & 0xff);
                            img.width = ((data.charCodeAt(++i) & 0xff) << 8) | (data.charCodeAt(++i) & 0xff);
                            break;
                        }
                    }
                    img.data = h ? h.substr(0, h.length - 2) + data.substr(2) : data;
                    t.ondata(img);
                    t._dictionary[id] = img;
                    return t;
                },
                
                _handleDefineButton: function(s, offset, len, frm, advanced){
                    var id = s.readUI16(),
                        t = this,
                        d = t._dictionary,
                        states = {},
                        button = {
                            type: "button",
                            id: id,
                            states: states,
                            trackAsMenu: advanced ? s.readBool(8) : false
                        };
                        if(advanced){ s.seek(2); }
                    do{
                        var flags = s.readUI8();
                        if(flags){
                            var objId = s.readUI16(),
                                depth = s.readUI16(),
                                state = 0x01,
                                character = {
                                    object: d[objId].id,
                                    depth: depth,
                                    matrix: s.readMatrix()
                                };
                                if(advanced){ character.cxform = s.readCxformA(); }
                            while(state <= 0x08){
                                if(flags & state){
                                    var list = states[state] || (states[state] = {});
                                    list[depth] = character;
                                }
                                state <<= 1;
                            }
                        }
                    }while(flags);
                    button.action = t._readAction(s, s.offset, len - (s.offset - offset));
                    t.ondata(button);
                    d[id] = button;
                    return t;
                },
                
                _readAction: function(s, offset, len){
                    s.seek(len - (s.offset - offset));
                    return '';
                },
                
                _handleJpegTables: function(s, offset, len){
                    this._jpegTables = s.readString(len);
                    return this;
                },
                
                _handleSetBackgroundColor: function(s, offset, len, frm){
                    frm.bgcolor = s.readRGB();
                    return this;
                },
                
                _handleDefineFont: function(s){
                    var id = s.readUI16(),
                        numGlyphs = s.readUI16() / 2,
                        glyphs = [],
                        t = this,
                        font = {
                            type: "font",
                            id: id,
                            glyphs: glyphs
                        };
                    s.seek(numGlyphs * 2 - 2);
                    while(numGlyphs--){ glyphs.push(t._readGlyph(s)); }
                    t.ondata(font);
                    t._dictionary[id] = font;
                    return t;
                },
                
                _readGlyph: function(s){
                    var numFillBits = s.readUB(4),
                        numLineBits = s.readUB(4),
                        x = 0,
                        y = 0,
                        cmds = [],
                        paths = [],	/* Ghostoy's Fix: simplify canvas renderer */
                        c = Gordon.styleChangeStates;
                    do{
                        var type = s.readUB(1),
                            flags = null;
                        if(type){
                            var isStraight = s.readBool(),
                                numBits = s.readUB(4) + 2;
                            if(isStraight){
                                var isGeneral = s.readBool();
                                if(isGeneral){
                                    x += s.readSB(numBits);
                                    y += s.readSB(numBits);
                                    cmds.push('L' + x + ',' + (-y));
                                    paths.push({
                                    	type: 'L',
                                    	x: x,
                                    	y: y
                                    });
                                }else{
                                    var isVertical = s.readBool();
                                    if(isVertical){
                                        y += s.readSB(numBits);
                                        cmds.push('V' + (-y));
                                        paths.push({
                                        	type: 'V',
                                        	x: x,
                                        	y: y
                                        });
                                    }else{
                                        x += s.readSB(numBits);
                                        cmds.push('H' + x);
                                        paths.push({
                                        	type: 'H',
                                        	x: x,
                                        	y: y
                                        });
                                    }
                                }
                            }else{
                                var cx = x + s.readSB(numBits),
                                    cy = y + s.readSB(numBits);
                                x = cx + s.readSB(numBits);
                                y = cy + s.readSB(numBits);
                                cmds.push('Q' + cx + ',' + (-cy) + ',' + x + ',' + (-y));
                                paths.push({
                                	type: 'Q',
                                	x: x,
                                	y: y,
                                	cx: cx,
                                	cy: cy
                                });
                            }
                        }else{
                            var flags = s.readUB(5);
                            if(flags){
                                if(flags & c.MOVE_TO){
                                    var numBits = s.readUB(5);
                                    x = s.readSB(numBits);
                                    y = s.readSB(numBits);
                                    cmds.push('M' + x + ',' + (-y));
                                    paths.push({
                                    	type: 'M',
                                    	x: x,
                                    	y: y
                                    });
                                }
                                if(flags & c.LEFT_FILL_STYLE || flags & c.RIGHT_FILL_STYLE){ s.readUB(numFillBits); }
                            }
                        }
                    }while(type || flags);
                    s.align();
                    return {commands: cmds.join(''), paths: paths};
                },
                
                _handleDefineText: function(s, offset, length, frm, withAlpha){
                    var id = s.readUI16(),
                        strings = [],
                        txt = {
                            type: "text",
                            id: id,
                            bounds: s.readRect(),
                            matrix: s.readMatrix(),
                            strings: strings
                        },
                        numGlyphBits = s.readUI8(),
                        numAdvBits = s.readUI8(),
                        fontId = null,
                        fill = null,
                        x = 0,
                        y = 0,
                        size = 0,
                        str = null,
                        d = this._dictionary;
                    do{
                        var hdr = s.readUB(8);
                        if(hdr){
                            var type = hdr >> 7;
                            if(type){
                                var flags = hdr & 0x0f;
                                if(flags){
                                    var f = Gordon.textStyleFlags;
                                    if(flags & f.HAS_FONT){ fontId = s.readUI16(); }
                                    if(flags & f.HAS_COLOR){ fill = withAlpha ? s.readRGBA() : s.readRGB(); }
                                    if(flags & f.HAS_XOFFSET){ x = s.readSI16(); }
                                    if(flags & f.HAS_YOFFSET){ y = s.readSI16(); }
                                    if(flags & f.HAS_FONT){ size = s.readUI16(); }
                                }
                                str = {
                                    font: d[fontId].id,
                                    fill: fill,
                                    x: x,
                                    y: y,
                                    size: size,
                                    entries: []
                                };
                                strings.push(str);
                            }else{
                                var numGlyphs = hdr & 0x7f,
                                    entries = str.entries;
                                while(numGlyphs--){
                                    var idx = s.readUB(numGlyphBits),
                                        adv = s.readSB(numAdvBits);
                                    entries.push({
                                        index: idx,
                                        advance: adv
                                    });
                                    x += adv;
                                }
                                s.align();
                            }
                        }
                    }while(hdr);
                    this.ondata(txt);
                    d[id] = txt;
                    return this;
                },
                
                _handleDoAction: function(s, offset, len, frm){
                    frm.action = this._readAction(s, offset, len);
                    return this;
                },
                
                _handleDefineFontInfo: function(s, offset, len){
                    var d = this._dictionary,
                        fontId = s.readUI16(),
                        font = d[fontId],
                        codes = [],
                        f = font.info = {
                            name: s.readString(s.readUI8()),
                            isSmall: s.readBool(3),
                            isShiftJIS: s.readBool(),
                            isANSI: s.readBool(),
                            isItalic: s.readBool(),
                            isBold: s.readBool(),
                            codes: codes
                        },
                        u = f.isUTF8 = s.readBool(),
                        i = font.glyphs.length;
                    while(i--){ codes.push(u ? s.readUI16() : s.readUI8()); }
                    this.ondata(font);
                    d[fontId] = font;
                    return this;
                },
                
                _handleDefineBitsLossless: function(s, offset, len, frm, withAlpha){
                    var id = s.readUI16(),
                        format = s.readUI8(),
                        img = {
                            type: "image",
                            id: id,
                            format: format,		/* Ghostoy */
                            width: s.readUI16(),
                            height: s.readUI16(),
                            withAlpha: withAlpha
                        };
                    if(format == Gordon.bitmapFormats.COLORMAPPED){ img.colorTableSize = s.readUI8() + 1; }
                    img.colorData = s.readString(len - (s.offset - offset));
                    this.ondata(img);
                    this._dictionary[id] = img;
                    return this;
                },
                
                _handleDefineBitsJpeg2: function(s, offset, len){
                    return this._handleDefineBits(s, offset, len);
                },
                
                _handleDefineShape2: function(s, offset, len){
                    return this._handleDefineShape(s, offset, len);
                },
                
                _handleDefineButtonCxform: function(s){
                    var t = this,
                        d = t._dictionary,
                        buttonId = s.readUI16(),
                        button = d[buttonId];
                    button.cxform = s.readCxform();
                    t.ondata(button);
                    d[buttonId] = button;
                    return t;
                },
                
                _handleProtect: function(s, offset, len){
                    s.seek(len);
                    return this;
                },
                
                _handlePlaceObject2: function(s, offset, len, frm, v3){
                    var flags = s.readUI8(),
                    	flags2 = (v3 ? s.readUI8() : 0),
                        depth = s.readUI16(),
                        f = Gordon.placeFlags,
                        f2 = Gordon.placeFlags2,
                        character = {depth: depth},
                        t = this;
                    if(v3 && ((flags2 & f2.HAS_CLASS_NAME) || (flags2 & f2.HAS_IMAGE) && (flags & f.HAS_CHARACTER))) {
                    	character.className = s.readString();
                    }
                    if(flags & f.HAS_CHARACTER){
                        var objId = s.readUI16();
                        character.object = t._dictionary[objId].id;
                    }
                    if(flags & f.HAS_MATRIX){ character.matrix = s.readMatrix(); }
                    if(flags & f.HAS_CXFORM){ character.cxform = s.readCxformA(); }
                    if(flags & f.HAS_RATIO){ character.ratio = s.readUI16(); }
                    if(flags & f.HAS_NAME){ character.name = s.readString(); }
                    if(flags & f.HAS_CLIP_DEPTH){ character.clipDepth = s.readUI16(); }
                    if(v3) {
                    	if(flags2 & f2.HAS_FILTER_LIST){ character.filterList = t._readFilterList(s); }
                    	if(flags2 & f2.HAS_BLEND_MODE){ character.blendMode = s.readUI8(); }
                    	if(flags2 & f2.HAS_CACHE_AS_BITMAP){ character.bitmapCache = s.readUI8(); }
                    }
                    
                    if(flags & f.HAS_CLIP_ACTIONS){ s.seek(len - (s.offset - offset)); }
                    frm.displayList[depth] = character;
                    return t;
                },
                
                _readFilterList: function(s) {
                	var num = s.readUI8(),
                		filters = [],
                		r = Gordon.filters,
                		f = null,
                		id = null;
                	while(num--) {
                		id = s.readUI8();
                		f = this['_read'+r[id]](s);
                		f.id = id;
                		filters.push(f);
                	}
                	return filters;
                },
                
                _readColorMatrixFilter: function(s) {
                	var num = 20,
                		matrix = [];
                	while(num--) {
                		matrix.push(s.readFloat());
                	}
                	return {matrix: matrix};
                },
                
                _readConvolutionFilter: function(s) {
                	var x = s.readUI8(),
                		y = s.readUI8(),
                		f = {
                			x: x,
                			y: y,
                			divisor: s.readFloat(),
                			bias: s.readFloat(),
                			matrix: s.read(x * y),
                			defaultColor: s.readRGBA()
                		},
                		flags = s.readUI8();
                	f.clamp = !!(flags & 0x02);
                	f.preserveAlpha = !!(flags & 0x01);
                	return f;
                },
                
                _readBlurFilter: function(s) {
                	return {
                		blurX: s.readFixed(),
                		blurY: s.readFixed(),
                		passes: s.readUB(5),
                		reserved: s.readUB(3)
                	};
                },
                
                _readDropShadowFilter: function(s) {
                	var f = {
                			dropShadowColor: s.readRGBA(),
                			blurX: s.readFixed(),
                			blurY: s.readFixed(),
                			angle: s.readFixed(),
                			distance: s.readFixed(),
                			strength: s.readFixed8()            			
                		},
                		flags = s.readUI8();
                	f.innerShadow = !!(flags & 0x80);
                	f.knockout = !!(flags & 0x40);
                	f.compositeSource = !!(flags & 0x20);
                	f.passes = flags & 0x1f;
                	return f;
                },
                
                _readGlowFilter: function(s) {
                	var f = {
                			glowColor: s.readRGBA(),
                			blurX: s.readFixed(),
                			blurY: s.readFixed(),
                			strength: s.readFixed8()
                		},
                		flags = s.readUI8();
                	f.innerGlow = !!(flags & 0x80);
                	f.knockout = !!(flags & 0x40);
                	f.compositeSource = !!(flags & 0x20);
                	f.passes = flags & 0x1f;
                	return f;
                },
                
                _readBevelFilter: function(s) {
                	var f = {
                			shadowColor: s.readRGBA(),
                			highlightColor: s.readRGBA(),
                			blurX: s.readFixed(),
                			blurY: s.readFixed(),
                			angle: s.readFixed(),
                			distance: s.readFixed(),
                			strength: s.readFixed8()
                		},
                		flags = s.readUI8();
                	f.innerShadow = !!(flags & 0x80);
                	f.knockout = !!(flags & 0x40);
                	f.compositeSource = !!(flags & 0x20);
                	f.onTop = !!(flags & 0x10);
                	f.passes = flags & 0x0f;
                	return f;
               },
               
               _readGradientGlowFilter: function(s) {
            	   var num = s.readUI8(),
            	   		colors = [],
            	   		ratio = [],
            	   		f = {};
            	   for(var i = 0; i < num; i++) {
            		   colors.push(s.readRGBA());
            	   }
            	   for(var i = 0; i < num; i++) {
            		   ratio.push(s.readUI8());
            	   }
            	   f.blurX = s.readFixed();
            	   f.blueY = s.readFixed();
            	   f.angle = s.readFixed();
            	   f.distance = s.readFixed();
            	   f.strength = s.readFixed8();
    	           f.innerShadow = !!(flags & 0x80);
    	           f.knockout = !!(flags & 0x40);
    	           f.compositeSource = !!(flags & 0x20);
    	           f.onTop = !!(flags & 0x10);
    	           f.passes = flags & 0x0f;
    	           return f;
               },
               
               _readGradientBevelFilter: function(s) {
            	   return this._readGradientGlowFilter(s);
               },
                
                _handlePlaceObject3: function(s, offset, len, frm) {
                	return this._handlePlaceObject2(s, offset, len, frm, true);
                },
                
                _handleRemoveObject2: function(s, offset, len, frm){
                    var depth = s.readUI16();
                    frm.displayList[depth] = null;
                    return this;
                },
                
                _handleDefineShape3: function(s, offset, len, frm){
                    return this._handleDefineShape(s, offset, len, frm, true);
                },
                
                _handleDefineText2: function(s, offset, len, frm){
                    return this._handleDefineText(s, offset, len, frm, true);
                },
                
                _handleDefineButton2: function(s, offset, len, frm){
                    return this._handleDefineButton(s, offset, len, frm, true);
                },
                
                _handleDefineBitsJpeg3: function(s, offset, len, frm){
                    return this._handleDefineBits(s, offset, len, frm, true);
                },
                
                _handleDefineBitsLossless2: function(s, offset, len, frm){
                    return this._handleDefineBitsLossless(s, offset, len, frm, true);
                },
                
                _handleDefineSprite: function(s, offset, len){
                    var id = s.readUI16(),
                        frameCount = s.readUI16(),
                        h = Gordon.tagHandlers,
                        f = Gordon.tagCodes.SHOW_FRAME,
                        c = Gordon.controlTags,
                        timeline = [],
                        sprite = {
                            id: id,
                            type: 'sprite',
                            timeline: timeline
                        },
                        t = this;
                    do{
                        var frm = {
                            type: "frame",
                            displayList: {}
                        };
                        do{
                            var hdr = s.readUI16(),
                                code = hdr >> 6,
                                len = hdr & 0x3f,
                                handl = h[code];
                            if(0x3f == len){ len = s.readUI32(); }
                            var offset = s.offset;
                            if(code){
    /*
                            	var tagName = (Gordon.tagNames[code] || code.toString(16)),
    	                    		iid = '';
    	                    	if(tagName.substring(0, 6) == 'DEFINE') {
    	                    		iid = s.readUI16();
    	                    		s.seek(-2);
    	                    	}
    	                    	console.info('>>'+tagName+':'+iid+':'+len);
    */
                                if(code == f){
                                    timeline.push(frm);
                                    frm = {
                                		type: "frame",
                                        displayList: {}
                                    };
                                    break;
                                }
                                if(c.indexOf(code) != -1 && t[handl]){ 
                                	t[handl](s, offset, len, frm);
                                }
                                else{ s.seek(len); }
                            }
                        }while(code);
                    }while(code);
                    t.ondata(sprite);
                    t._dictionary[id] = sprite;
                    return t;
                },
                
                _handleFrameLabel: function(s, offset, len, frm){
                    frm.label = s.readString();
                    return this;
                },
                
                _handleDefineMorphShape: function(s, offset, len){
                    var id = s.readUI16(),
                        startBounds = s.readRect(),
                        endBounds = s.readRect(),
                        endEdgesOffset = s.readUI32(),
                        t = this,
                        fillStyles = t._readFillStyles(s, true, true),
                        lineStyles = t._readLineStyles(s, true, true),
                        morph = {
                            type: "morph",
                            id: id,
                            startEdges: t._readEdges(s, fillStyles, lineStyles, true, true),
                            endEdges: t._readEdges(s, fillStyles, lineStyles, true, true)
                        };
                    t.ondata(morph);
                    t._dictionary[id] = morph;
                    return t;
                },
                
                _handleDefineFont2: function(s, offset, len, frm, extended){
                    var id = s.readUI16(),
                        hasLayout = s.readBool(),
                        glyphs = [],
                        font = {
                            type: "font",
                            id: id,
                            glyphs: glyphs,
                            extended: !!extended
                        },
                        codes = [],
                        f = font.info = {
                            isShiftJIS: s.readBool(),
                            isSmall: s.readBool(),
                            isANSI: s.readBool(),
                            useWideOffsets: s.readBool(),
                            isUTF8: s.readBool(),
                            isItalic: s.readBool(),
                            isBold: s.readBool(),
                            languageCode: s.readLanguageCode(),
                            name: s.readString(s.readUI8()),
                            codes: codes
                        },
                        i = numGlyphs = s.readUI16(),
                        w = f.useWideOffsets,
                        offsets = [],
                        tablesOffset = s.offset,
                        u = f.isUTF8;
                    while(i--){ offsets.push(w ? s.readUI32() : s.readUI16()); }
                    s.seek(w ? 4 : 2);
                    for(var i = 0, o = offsets[0]; o; o = offsets[++i]){
                        s.seek(tablesOffset + o, true);
                        glyphs.push(this._readGlyph(s));
                    }
                    var i = numGlyphs;
                    while(i--){ codes.push(u ? s.readUI16() : s.readUI8()); };
                    if(hasLayout){
                        f.ascent = s.readUI16();
                        f.descent = s.readUI16();
                        f.leading = s.readUI16();
                        var advanceTable = f.advanceTable = [],
                            boundsTable = f.boundsTable = [],
                            kerningTable = f.kerningTable = [];
                        i = numGlyphs;
                        while(i--){ advanceTable.push(s.readUI16()); };
                        i = numGlyphs;
                        while(i--){ boundsTable.push(s.readRect()); };
                        var kerningCount = s.readUI16();
                        while(kerningCount--){ kerningTable.push({
                            code1: u ? s.readUI16() : s.readUI8(),
                            code2: u ? s.readUI16() : s.readUI8(),
                            adjustment: s.readUI16()
                        }); }
                    }
                    this.ondata(font);
                    this._dictionary[id] = font;
                    return this;
                },
                _handleDefineFont3: function(s, offset, len, frm) {
                	return this._handleDefineFont2(s, offset, len, frm, true);
                },
                _handleDefineEditText: function(s, offset, len) {
                	var t = this,
                		d = t._dictionary,
                		id = s.readUI16(),
                		bounds = s.readRect(),
                		flags = s.readUI16(),
                		txt = {
                			type: 'edit-text',
                			id: id,
                			bounds: bounds,
                			wordWrap: !!(flags & 0x4000),
                			multiline: !!(flags && 0x2000),
                			password: !!(flags && 0x1000),
                			readOnly: !!(flags && 0x0800),
                			autoSize: !!(flags && 0x0040),
                			noSelect: !!(flags && 0x0010),
                			border: !!(flags && 0x0008),
                			wasStatic: !!(flags && 0x0004),
                			html: !!(flags && 0x0002),
                			useOutlines: !!(flags && 0x0001)
                		};
                	if(flags & 0x0100) txt.font = d[s.readUI16()].id;
                	if(flags & 0x0080) txt.fontClass = s.readString();
                	if(flags & 0x0100) txt.fontHeight = s.readUI16();
                	if(flags & 0x0400) txt.color = s.readRGBA();
                	if(flags & 0x0200) txt.maxLength = s.readUI16();
                	if(flags & 0x0020) {
                		txt.align = s.readUI8();
                		txt.leftMargin = s.readUI16();
                		txt.rightMargin = s.readUI16();
                		txt.indent = s.readUI16();
                		txt.leading = s.readSI16();
                	}
            		txt.variableName = s.readString();
            		if(flags & 0x8000) txt.initialText = s.readString();
            		
                	t.ondata(txt);
                	t._dictionary[id] = txt;
                	return t;
                }
            };
            
            function nlizeMatrix(matrix){
                return {	/* Ghostoy's Fix: multiply by 20 to fix gradient bug in FF */
                    scaleX: matrix.scaleX * 20, scaleY: matrix.scaleY * 20,
                    skewX: matrix.skewX * 20, skewY: matrix.skewY * 20,
                    moveX: matrix.moveX, moveY: matrix.moveY
                };
            }
            
            function cloneEdge(edge){
                return {
                    i: edge.i,
                    f: edge.f,
                    x1: edge.x1, y1: edge.y1,
                    cx: edge.cx, cy: edge.cy,
                    x2: edge.x2, y2: edge.y2
                };
            }
            
            function edges2cmds(edges, stroke){
                var firstEdge = edges[0],
                    x1 = 0,
                    y1 = 0,
                    x2 = 0,
                    y2 = 0,
                    cmds = [];
                for(var i = 0, edge = firstEdge; edge; edge = edges[++i]){
                    x1 = edge.x1;
                    y1 = edge.y1;
                    if(x1 != x2 || y1 != y2 || !i){ cmds.push('M' + x1 + ',' + y1); }
                    x2 = edge.x2;
                    y2 = edge.y2;
                    if(null == edge.cx || null == edge.cy){
                        if(x2 == x1){ cmds.push('V' + y2); }
                        else if(y2 == y1){ cmds.push('H' + x2); }
                        else{ cmds.push('L' + x2 + ',' + y2); }
                    }else{ cmds.push('Q' + edge.cx + ',' + edge.cy + ',' + x2 + ',' + y2); }
                };
                if(!stroke && (x2 != firstEdge.x1 || y2 != firstEdge.y1)){ cmds.push('L' + firstEdge.x1 + ',' + firstEdge.y1); }
                return cmds.join('');
            }
            
            function pt2key(x, y){
                return (x + 50000) * 100000 + y;
            }
            
            win.onmessage = function(e){
                new Gordon.Parser(e.data);
            };
        }
    })();
    
    (function(){
        var LOCATION_DIRNAME = win.location.href.replace(/[^\/]*$/, ''),
            defaults = {
                id: '',
                width: 0,
                height: 0,
                autoplay: true,
                loop: true,
                quality: Gordon.qualityValues.HIGH,
                scale: Gordon.scaleValues.SHOW_ALL,
                bgcolor: '',
                poster: '',
                renderer: null,
                onprogress: function(percent){},
                onreadystatechange: function(state){}
            };
            
        Gordon.Movie = function(url, options){
            var t = this,
                s = Gordon.readyStates;
            t.url = url;
            for(var prop in defaults){ t[prop] = prop in options ? options[prop] : defaults[prop]; }
            if(!url){ throw new Error("URL of a SWF movie file must be passed as first argument"); }
            t.framesLoaded = 0;
            t.isPlaying = false;
            t.currentFrame = 0;
            t.currentLabel = undefined;
            t.times = [0, 0];
            t._readyState = s.UNINITIALIZED;
            t._changeReadyState(t._readyState);
            var d = t._dictionary = {},
                l = t._timeline = [];
            t._changeReadyState(s.LOADING);
            new Gordon.Parser((/^\w:\/\//.test(url) ? '' : LOCATION_DIRNAME) + url, function(obj){
                var action = obj.action;
                if(action){ eval("obj.action = function(){ " + action + "; }"); }
                switch(obj.type){
                    case "header":
                        for(var prop in obj){ t['_' + prop] = obj[prop]; }
                        var f = t._frameSize,
                            r = t.renderer = t.renderer || Gordon.SvgRenderer,
                            id = t.id;
                        if(!(t.width && t.height)){
                            t.width = (f.right - f.left) / 20;
                            t.height = (f.bottom - f.top) / 20;
                        };
                        t._renderer = new r(t.width, t.height, f, t.quality, t.scale, t.bgcolor);
                        t.totalFrames = t._frameCount;
                        if(id){
                            var stage = t._stage = doc.getElementById(id),
                                bgcolor = t.bgcolor,
                                bgParts = [],
                                poster = t.poster;
                            stage.innerHTML = '';
                            if(t.bgcolor){ bgParts.push(bgcolor); }
                            if(poster){ bgParts.push(poster, "center center"); }
                            if(bgParts.length){ stage.setAttribute("style", "background: " + bgParts.join(' ')); }
                        }
                        t._changeReadyState(s.LOADED);
                        break;
                    case "frame":
                        t._renderer.frame(obj);
                        l.push(obj);
                        var lbl = obj.label,
                            n = ++t.framesLoaded;
                        if(lbl){ t._labeledFrameNums[lbl] = n; }
                        t.onprogress(~~((n * 100) / t.totalFrames));
                        if(1 == n){
                            var stage = t._stage;
                            if(stage){
                                stage.appendChild(t._renderer.node);
                                t._changeReadyState(s.INTERACTIVE);
                            }
                            if(t.autoplay){ t.play(); }
                            else{ t.goTo(1); }
                        }
                        if(n == t.totalFrames){ t._changeReadyState(s.COMPLETE); }
                        break;
                    case "debug":   // parsing time
                        t.times[0] = obj.msg;
                        break;
                    default:
                        var startTime = new Date();
                        t._renderer.define(obj);
                        d[obj.id] = obj;
                        t.times[1] += new Date() - startTime;
                }
            });
        };
        Gordon.Movie.prototype = {
            _changeReadyState: function(state){
                this._readyState = state;
                this.onreadystatechange(state);
                return this;
            },
            
            play: function(){
                var t = this,
                    c = t.currentFrame,
                    timeout = 1000 / t._frameRate;
                t.isPlaying = true;
                if(c < t.totalFrames){
                    if(t.framesLoaded > c){ t.goTo(c + 1); }
                    else{ timeout = 0; }
                }else{
                    if(!t.loop){ return t.stop(); }
                    else{ t.rewind(); }
                }
                setTimeout(function(){
                    if(t.isPlaying){ t.play(); };
                }, timeout);
                return t;
            },
            
            next: function(){
                var t = this,
                    c = t.currentFrame;
                t.goTo(c < t.totalFrames ? c + 1 : 1);
                return t;
            },
            
            goTo: function gf(frmNumOrLabel){
                var t = this,
                    c = t.currentFrame,
                    r = t._renderer;
                if(gf.caller !== t.play && gf.caller !== t.rewind){ t.stop(); }
                if(isNaN(frmNumOrLabel)){
                    var frmNum = t._labeledFrameNums[frmNumOrLabel];
                    if(frmNum){ t.goTo(frmNum); }
                }else if(frmNumOrLabel != c){
                    if(frmNumOrLabel < c){ c = t.currentFrame = 0; }
                    var l = t._timeline;
                    while(c != frmNumOrLabel){
                        c = ++t.currentFrame;
                        var idx = c - 1,
                            frm = l[idx],
                            action = frm.action,
                            start = new Date;
                        r.show(idx);
                        t.times.push(new Date - start);
                        t.currentLabel = frm.lbl;
                        if(action){ action.call(this); }
                    }
                }
                return t;
            },
            
            stop: function(){
                this.isPlaying = false;
                return this;
            },
            
            prev: function(){
                var t = this,
                    c = t.currentFrame;
                t.goTo(c > 1 ? c - 1 : t.totalFrames);
                return t;
            },
            
            rewind: function(){
            	if(this._renderer.init) {
            		this._renderer.init();
            	}
                this.goTo(1);
                return this;
            },
            
            getURL: function(url, target){
                var u = Gordon.urlTargets;
                switch(target){
                    case u.BLANK:
                        win.open(url);
                        break;
                    case u.PARENT:
                        win.parent.location.href = url;
                        break;
                    case u.TOP:
                        win.top.location.href = url;
                        break;
                    default:
                        win.location.href = url;
                }
                return this;
            },
            
            toggleQuality: function thq(){
                var o = thq._quality,
                    t = this,
                    q = t.quality;
                if(o){
                    q = t.quality = o;
                    thq._quality = null;
                }else{ t.quality = thq._quality = q; }
                t._renderer.setQuality(q);
                return t;
            }
        };
    })();
    
    (function(){
        var NS_SVG = "http://www.w3.org/2000/svg",
            NS_XLINK = "http://www.w3.org/1999/xlink",
            NS_XHTML = "http://www.w3.org/1999/xhtml",
            b = Gordon.buttonStates,
            buttonStates = {},
            buttonMask = 0;
        for(var state in b){ buttonStates[b[state]] = state.toLowerCase(); }
        
        Gordon.SvgRenderer = function(width, height, frmSize, quality, scale, bgcolor){
            var t = this,
                n = t.node = t._createElement("svg"),
                attrs = {
                    width: width,
                    height: height
                },
                viewWidth = frmSize.right - frmSize.left,
                viewHeight = frmSize.bottom - frmSize.top;
            t.width = width;
            t.height = height;
            t.viewWidth = viewWidth;
            t.viewHeight = viewHeight;
            t.quality = quality || Gordon.qualityValues.HIGH;
            t.scale = scale || Gordon.scaleValues.SHOW_ALL;
            t.bgcolor = bgcolor;
            if(viewWidth && viewHeight && (width != viewWidth || height != viewHeight)){
                attrs.viewBox = [0, 0, viewWidth, viewHeight] + '';
                if(scale == Gordon.scaleValues.EXACT_FIT){ attrs.preserveAspectRatio = "none"; }
            }
            t._setAttributes(n, attrs);
            t._defs = n.appendChild(t._createElement("defs"));
            var s = t._stage = n.appendChild(t._createElement('g'));
            t._setAttributes(s, {
                "fill-rule": "evenodd",
                "stroke-linecap": "round",
                "stroke-linejoin": "round"
            });
            t.setQuality(t.quality);
            if(bgcolor){ t.setBgcolor(bgcolor); }
            t._dictionary = {};
            t._fills = {};
            t._cast = {};
            t._timeline = [];
            t._displayList = {};
            t._eventTarget = null;
        };
        Gordon.SvgRenderer.prototype = {
            _createElement: function(name){
                return doc.createElementNS(NS_SVG, name);
            },
            
            _setAttributes: function(node, attrs, ns){
                for(var name in attrs){
                    if(ns){ node.setAttributeNS(ns, name, attrs[name]); }
                    else{ node.setAttribute(name, attrs[name]); }
                }
                return node;
            },
            
            setQuality: function(quality){
                var q = Gordon.qualityValues,
                    t = this;
                switch(quality){
                    case q.LOW:
                        var attrs = {
                            "shape-rendering": "crispEdges",
                            "image-rendering": "optimizeSpeed",
                            "text-rendering": "optimizeSpeed",
                            "color-rendering": "optimizeSpeed"
                        }
                        break;
                    case q.AUTO_LOW:
                    case q.AUTO_HIGH:
                        var attrs = {
                            "shape-rendering": "auto",
                            "image-rendering": "auto",
                            "text-rendering": "auto",
                            "color-rendering": "auto"
                        }
                        break;
                    case q.MEDIUM:
                        var attrs = {
                            "shape-rendering": "optimizeSpeed",
                            "image-rendering": "optimizeSpeed",
                            "text-rendering": "optimizeLegibility",
                            "color-rendering": "optimizeSpeed"
                        }
                        break;
                    case q.HIGH:
                        var attrs = {
                            "shape-rendering": "geometricPrecision",
                            "image-rendering": "auto",
                            "text-rendering": "geometricPrecision",
                            "color-rendering": "optimizeQuality"
                        }
                        break;
                    case q.BEST:
                        var attrs = {
                            "shape-rendering": "geometricPrecision",
                            "image-rendering": "optimizeQuality",
                            "text-rendering": "geometricPrecision",
                            "color-rendering": "optimizeQuality"
                        }
                        break;
                }
                t._setAttributes(t._stage, attrs);
                t.quality = quality;
                return t;
            },
            
            setBgcolor: function(rgb){
                var t = this;
                if(!t.bgcolor){
                    t.node.style.background = color2string(rgb);
                    t.bgcolor = rgb;
                }
                return t;
            },
            
            define: function(obj){
                var id = obj.id,
                    t = this,
                    d = t._dictionary,
                    item = d[id],
                    type = obj.type,
                    node = null,
                    attrs = {id: type[0] + id};
                if(!item || !item.node){
                    switch(type){
                        case "shape":
                            var segments = obj.segments;
                            if(segments){
                                var node = t._createElement('g'),
                                    frgmt = doc.createDocumentFragment();
                                for(var i = 0, seg = segments[0]; seg; seg = segments[++i]){
                                    var segNode = frgmt.appendChild(t._buildShape(seg));
                                    t._setAttributes(segNode, {id: 's' + seg.id})
                                }
                                node.appendChild(frgmt);
                            }else{ var node = t._buildShape(obj); }
                            break;
                        case "image":
                            var node = t._createElement("image"),
                                colorData = obj.colorData,
                                width = obj.width,
                                height = obj.height;
                            if(colorData){
                                var colorTableSize = obj.colorTableSize || 0,
                                    bpp = (obj.withAlpha ? 4 : 3),
                                    cmIdx = colorTableSize * bpp,
                                    data = (new Gordon.Stream(colorData)).unzip(true),
                                    withAlpha = obj.withAlpha,
                                    pxIdx = 0,
                                    canvas = doc.createElement("canvas"),
                                    ctx = canvas.getContext("2d"),
                                    imgData = ctx.getImageData(0, 0, width, height),
                                    pxData = imgData.data,
                                    pad = colorTableSize ? ((width + 3) & ~3) - width : 0
                                canvas.width = width;
                                canvas.height = height;
                                for(var y = 0; y < height; y++){
                                    for(var x = 0; x < width; x++){
                                        var idx = (colorTableSize ? data[cmIdx++] : cmIdx) * bpp,
                                            alpha = withAlpha ? data[cmIdx + 3] : 255;
                                        if(alpha){
                                            pxData[pxIdx] = data[idx];
                                            pxData[pxIdx + 1] = data[idx + 1];
                                            pxData[pxIdx + 2] = data[idx + 2];
                                            pxData[pxIdx + 3] = alpha;
                                        }
                                        pxIdx += 4;
                                    }
                                    cmIdx += pad;
                                }
                                ctx.putImageData(imgData, 0, 0);
                                var uri = canvas.toDataURL();
                            }else{
                                var alphaData = obj.alphaData,
                                    uri = "data:image/jpeg;base64," + btoa(obj.data);
                                if(alphaData){
                                    var data = (new Gordon.Stream(alphaData)).unzip(true),
                                        img = new Image(),
                                        canvas = doc.createElement("canvas"),
                                        ctx = canvas.getContext("2d");
                                    img.src = uri;
                                    canvas.width = width;
                                    canvas.height = height;
                                    ctx.drawImage(img, 0, 0);
                                    var len = width * height;
                                        imgData = ctx.getImageData(0, 0, width, height),
                                        pxData = imgData.data,
                                        pxIdx = 0;
                                    for(var i = 0; i < len; i++){
                                        pxData[pxIdx + 3] = data[i];
                                        pxIdx += 4;
                                    }
                                    ctx.putImageData(imgData, 0, 0);
                                    uri = canvas.toDataURL();
                                }
                            }
                            t._setAttributes(node, {href: uri}, NS_XLINK);
                            attrs.width = width;
                            attrs.height = height;
                            break;
                        case "font":
                            var info = obj.info;
                            if(info){
                                var node = t._createElement("font"),
                                    faceNode = node.appendChild(t._createElement("font-face")),
                                    advanceTable = info.advanceTable
                                    glyphs = obj.glyphs,
                                    codes = info.codes,
                                    frgmt = doc.createDocumentFragment(),
                                    kerningTable = info.kerningTable;
                                t._setAttributes(faceNode, {
                                    "font-family": id,
                                    "units-per-em": 20480,
                                    ascent: info.ascent || 20480,
                                    descent: info.ascent || 20480,
                                    "horiz-adv-x": advanceTable ? '' + advanceTable : 20480
                                });
                                for(var i = 0, glyph = glyphs[0]; glyph; glyph = glyphs[++i]){
                                    var cmds = glyph.commands,
                                        code = codes[i];
                                    if(cmds && code){
                                        var glyphNode = frgmt.appendChild(t._createElement("glyph"));
                                        t._setAttributes(glyphNode, {
                                            unicode: String.fromCharCode(code),
                                            d: glyph.commands
                                        });
                                    }
                                }
                                if(kerningTable){
                                    for(var i = 0, kern = kerningTable[0]; kern; kern = kerningTable[++i]){
                                        var kernNode = frgmt.appendChild(t._createElement("hkern"));
                                        t._setAttributes(kernNode, {
                                            g1: kern.code1,
                                            g2: kern.code2,
                                            k: kern.adjustment
                                        });
                                    }
                                }
                                node.appendChild(frgmt);
                            }
                            break;
                        case "text":
                            var frgmt = doc.createDocumentFragment(),
                                strings = obj.strings;
                            for(var i = 0, string = strings[0]; string; string = strings[++i]){
                                var txtNode = frgmt.appendChild(t._createElement("text")),
                                    entries = string.entries,
                                    font = t._dictionary[string.font].object,
                                    info = font.info,
                                    codes = info.codes,
                                    advances = [],
                                    chars = [];
                                    x = string.x,
                                    y = string.y * -1;
                                for(var j = 0, entry = entries[0]; entry; entry = entries[++j]){
                                    var str = String.fromCharCode(codes[entry.index]);
                                    if(str != ' ' || chars.length){
                                        advances.push(x);
                                        chars.push(str);
                                    }
                                    x += entry.advance;
                                }
                                t._setAttributes(txtNode, {
                                    id: 't' + id + '-' + (i + 1),
                                    "font-family": font.id,
                                    "font-size": string.size * 20,
                                    x: advances.join(' '),
                                    y: y
                                });
                                txtNode.appendChild(doc.createTextNode(chars.join('')));
                            }
                            if(strings.length > 1){
                                var node = t._createElement('g');
                                node.appendChild(frgmt);
                            }else{ var node = frgmt.firstChild; }
                            break;
                    }
                    if(node){
                        t._setAttributes(node, attrs);
                        t._defs.appendChild(node);
                    }
                    d[id] = {
                        object: obj,
                        node: node
                    }
                }else{ d[id].object = obj; }
                return t;
            },
            
            _buildShape: function(shape){
                var fill = shape.fill,
                    t = this;
                if(fill && "pattern" == fill.type && !fill.repeat){
                    var node = t._createElement("use"),
                        img = fill.image;
                    t._setAttributes(node, {href: "#" + img.id}, NS_XLINK);
                    t._setAttributes(node, {transform: matrix2string(fill.matrix)});
                }else{
                    var node = t._createElement("path");
                    t._setAttributes(node, {d: shape.commands});
                }
                return node;
            },
            
            frame: function(frm){
                var bgcolor = frm.bgcolor,
                    t = this,
                    d = frm.displayList;
                if(bgcolor && !t.bgcolor){
                    t.setBgcolor(bgcolor);
                    t.bgcolor = bgcolor;
                }
                for(depth in d){
                    var character = d[depth];
                    if(character){
                        var objId = character.object || t._displayList[depth].character.object;
                        if(objId){
                            if(character.clipDepth){
                                var cpNode = t._defs.appendChild(t._createElement("clipPath")),
                                    useNode = cpNode.appendChild(t._createElement("use")),
                                    matrix = character.matrix;
                                t._setAttributes(useNode, {id: 'p' + objId});
                                t._setAttributes(useNode, {href: '#s' + objId}, NS_XLINK);
                                if(matrix){ t._setAttributes(useNode, {transform: matrix2string(matrix)}); }
                            }
                            var cxform = character.cxform,
                                characterId = character._id = objectId({
                                    object: objId,
                                    cxform: cxform
                                }),
                                c = t._cast[characterId],
                                node = c ? c.node : t._prepare(t._dictionary[objId].object, cxform);
                            t._setAttributes(node, {id: 'c' + characterId});
                            t._defs.appendChild(node);
                        }
                        t._cast[characterId] = {
                            character: character,
                            node: node
                        };
                    }
                }
                t._timeline.push(frm);
                return t;
            },
            
            _prepare: function(obj, cxform){
                var type = obj.type,
                    t = this,
                    node = null,
                    id = obj.id,
                    attrs = {};
                switch(type){
                    case "shape":
                        var segments = obj.segments;
                        if(segments){
                            var node = t._createElement('g'),
                                frgmt = doc.createDocumentFragment();
                            for(var i = 0, seg = segments[0]; seg; seg = segments[++i]){
                                frgmt.appendChild(t._prepare(seg, cxform));
                            }
                            node.appendChild(frgmt);
                        }else{
                            var node = t._createElement("use");
                            t._setAttributes(node, {href: '#s' + id}, NS_XLINK);
                            t._setStyle(node, obj.fill, obj.line, cxform);
                        }
                        break;
                    case "button":
                        var node = t._createElement('g'),
                            frgmt = doc.createDocumentFragment(),
                            states = obj.states,
                            hitNode = null,
                            stateNodes = {},
                            currState = b.UP,
                            m = Gordon.mouseButtons,
                            isMouseOver = false,
                            action = obj.action,
                            trackAsMenu = obj.trackAsMenu;
                        for(var state in states){
                            var stateFrgmt = doc.createDocumentFragment(),
                                list = states[state];
                            for(var depth in list){
                                var character = list[depth];
                                stateFrgmt.appendChild(t._prepare(t._dictionary[character.object].object, obj.cxform));
                            }
                            if(stateFrgmt.length > 1){
                                var stateNode = t._createElement('g');
                                stateNode.appendChild(stateFrgmt);
                            }else{ var stateNode = stateFrgmt.firstChild; }
                            t._setAttributes(stateNode, {opacity: state == b.UP ? 1 : 0});
                            if(state == b.HIT){ hitNode = stateNode; }
                            else{ stateNodes[state] = frgmt.appendChild(stateNode); }
                        }
                        node.appendChild(frgmt);
                        node.appendChild(hitNode);
                        
                        function setState(state){
                            t._setAttributes(stateNodes[currState], {opacity: 0});
                            t._setAttributes(stateNodes[state], {opacity: 1});
                            currState = state;
                        };
                        
                        function mouseupHandle(e){
                            if(!(buttonMask & m.LEFT)){
                                if(isMouseOver){
                                    setState(b.OVER);
                                    if(action){ action(); }
                                }else{ setState(b.UP); }
                                doc.removeEventListener("mouseup", mouseupHandle, false);
                                t.eventTarget = null;
                            }
                            return false;
                        };
                        
                        hitNode.onmousemove = function(e){
                            if(!t.eventTarget){
                                if(buttonMask & m.LEFT){ this.onmousedown(e); }
                                else{ setState(b.OVER); }
                            }  
                            if(!isMouseOver){
                                var handle = doc.addEventListener("mousemove", function(){
                                    if(!t.eventTarget || trackAsMenu){ setState(b.UP); }
                                    doc.removeEventListener("mousemove", handle, true);
                                    isMouseOver = false;
                                }, true);
                            }
                            isMouseOver = true;
                            return false;
                        };
                        
                        hitNode.onmousedown = function(e){
                            if(buttonMask & m.LEFT){
                                setState(b.DOWN);
                                doc.addEventListener("mouseup", mouseupHandle, false);
                                t.eventTarget = this;
                            }
                            return false;
                        };
                        
                        hitNode.onmouseup = function(e){
                            setState(b.OVER);
                            return false;
                        };
                        break;
                    case "text":
                        var strings = obj.strings,
                            frgmt = doc.createDocumentFragment(),
                            matrix = cloneMatrix(obj.matrix);
                        for(var i = 0, string = strings[0]; string; string = strings[++i]){
                            var useNode = frgmt.appendChild(t._createElement("use"));
                            t._setAttributes(useNode, {href: '#t' + id + '-' + (i + 1)}, NS_XLINK);
                            t._setStyle(useNode, string.fill, null, cxform);
                        }
                        if(strings.length > 1){
                            var node = t._createElement('g');
                            node.appendChild(frgmt);
                        }else{ var node = frgmt.firstChild; }
                        matrix.scaleY *= -1;
                        attrs.transform = matrix2string(matrix);
                        break;
                }
                if(node){ t._setAttributes(node, attrs); }
                return node;
            },
            
            _setStyle: function(node, fill, line, cxform){
                var t = this,
                    attrs = {};
                if(fill){
                    var type = fill.type;
                    if(fill.type){
                        objectId(fill);
                        var fillNode = t._defs.appendChild(t._buildFill(fill, cxform));
                        attrs.fill = "url(#" + fillNode.id + ')';
                    }else{
                        var color = cxform ? transformColor(fill, cxform) : fill,
                            alpha = color.alpha / 255;
                        attrs.fill = color2string(color);
                        if(undefined != alpha && alpha < 1){ attrs["fill-opacity"] = alpha; }
                    }
                }else{ attrs.fill = "none"; }
                if(line){
                    var color = cxform ? transformColor(line.color, cxform) : line.color,
                        alpha = color.alpha / 255;
                    attrs.stroke = color2string(color);
                    attrs["stroke-width"] = Math.max(line.width, 1);
                    if(undefined != alpha && alpha < 1){ attrs["stroke-opacity"] = alpha; }
                }
                t._setAttributes(node, attrs);
                return t;
            },
            
            _buildFill: function(fill, cxform){
                var t = this,
                    f = t._fills,
                    id = objectId(fill),
                    node = f[id];
                if(!node){
                    var type = fill.type,
                        attrs = {id: type[0] + id};
                    switch(type){
                        case "linear":
                        case "radial":
                            var node = t._createElement(type + "Gradient"),
                                s = Gordon.spreadModes,
                                i = Gordon.interpolationModes,
                                stops = fill.stops;
                            attrs.gradientUnits = "userSpaceOnUse";
                            attrs.gradientTransform = matrix2string(fill.matrix);
                            if("linear" == type){ 
                                attrs.x1 = -819.2;
                                attrs.x2 = 819.2;
                            }else{
                                attrs.cx = attrs.cy = 0;
                                attrs.r = 819.2;
                            }
                            switch(fill.spread){
                                case s.REFLECT:
                                    attrs.spreadMethod = "reflect";
                                    break;
                                case s.REPEAT:
                                    attrs.spreadMethod = "repeat";
                                    break;
                            }
                            if(fill.interpolation == i.LINEAR_RGB){ attrs["color-interpolation"] = "linearRGB"; }
                            stops.forEach(function(stop){
                                var stopNode = node.appendChild(t._createElement("stop")),
                                    color = cxform ? transformColor(stop.color, cxform) : stop.color,
                                    alpha = color.alpha / 255;
                                t._setAttributes(stopNode, {
                                    offset: stop.offset,
                                    "stop-color": color2string(color),
                                    "stop-opacity": alpha == undefined ? 1 : alpha
                                });
                            });
                            break;
                        case "pattern":
                            var node = t._createElement("pattern");
                            if(cxform){
                                var canvas = doc.createElement("canvas"),
                                    img = doc.getElementById('i' + obj.image.id),
                                    width = img.width,
                                    height = img.height,
                                    ctx = canvas.getContext("2d");
                                canvas.width = width;
                                canvas.height = height;
                                ctx.drawImage(img, 0, 0);
                                var imgData = ctx.getImageData(0, 0, width, height),
                                    pxData = imgData.data,
                                    multR = cxform.multR,
                                    multG = cxform.multG,
                                    multB = cxform.multB,
                                    multA = cxform.multA,
                                    addR = cxform.addR,
                                    addG = cxform.addG,
                                    addB = cxform.addB,
                                    addA = cxform.addA;
                                for(var i = 0; undefined != pxData[i]; i+= 4){
                                    pxData[i] = ~~Math.max(0, Math.min((pxData[i] * multR) + addR, 255));
                                    pxData[i + 1] = ~~Math.max(0, Math.min((pxData[i + 1] * multG) + addG, 255));
                                    pxData[i + 2] = ~~Math.max(0, Math.min((pxData[i + 2] * multB) + addB, 255));
                                    pxData[i + 3] = ~~Math.max(0, Math.min((pxData[i + 3] * multA) + addA, 255));
                                }
                                var imgNode = node.appendChild(t._createElement("image"));
                                t._setAttributes(imgNode, {href: canvas.toDataURL()}, NS_XLINK);
                                t._setAttributes(imgNode, {
                                    width: width,
                                    height: height
                                });
                            }else{
                                var useNode = node.appendChild(t._createElement("use")),
                                    img = fill.image;
                                t._setAttributes(useNode, {href: "#i" + img.id}, NS_XLINK);
                            }
                            attrs.patternUnits = "userSpaceOnUse";
                            attrs.patternTransform = matrix2string(fill.matrix);
                            attrs.width = img.width;
                            attrs.height = img.height;
                            break;
                    }
                    t._setAttributes(node, attrs);
                    t._fills[id] = node;
                }
                return node;
            },
            
            show: function(frmIdx){
                var t = this,
                    frm = t._timeline[frmIdx],
                    d = frm.displayList;
                for(var depth in d){
                    var character = d[depth];
                    if(character){ t.place(character); }
                    else{ t.remove(depth); }
                }
                return t;
            },
            
            place: function(character){
                var depth = character.depth,
                    t = this,
                    d = t._displayList,
                    replace = d[depth];
                if(replace && !character.object){ var node = replace.node; }
                else{
                    if(character.clipDepth){
                        var node = t._createElement('g');
                        t._setAttributes(node, {"clip-path": "url(#p" + character.object + ')'});
                    }else{ var node = t._createElement("use"); }
                    var stage = t._stage;
                    if(replace){ t.remove(depth); }
                    if(1 == depth){ stage.insertBefore(node, stage.firstChild); }
                    else{
                        var nextDepth = 0;
                        for(var entry in d){
                            var c = d[entry].character;
                            if(c.clipDepth && depth <= c.clipDepth){ stage = d[entry].node; }
                            if(entry > depth){
                                nextDepth = entry;
                                break;
                            }
                        }
                        if(nextDepth){ stage.insertBefore(node, d[nextDepth].node); }
                        else{ stage.appendChild(node); }
                    }
                }
                if(!character.clipDepth){
                    var attrs = {},
                        matrix = character.matrix;
                    if(matrix){ attrs.transform = matrix2string(matrix); }
                    t._setAttributes(node, {href: "#c" + character._id}, NS_XLINK);
                    t._setAttributes(node, attrs);
                }
                d[depth] = {
                    character: character,
                    node: node
                };
                return t;
            },
            
            remove: function(depth){
                var d = this._displayList,
                    item = d[depth],
                    node = item.node,
                    parentNode = node.parentNode;
                if(item.character.clipDepth){
                    var childNodes = node.childNodes;
                    for(var c in childNodes){ parentNode.insertBefore(childNodes[c], node); }
                }
                parentNode.removeChild(node);
                delete d[depth];
                return this;
            }
        };
        
        var REGEXP_IS_COLOR = /^([\da-f]{1,2}){3}$/i;
        
        function color2string(color){
            if("string" == typeof color){ return REGEXP_IS_COLOR.test(color) ? color : null; }
            return "rgb(" + [color.red, color.green, color.blue] + ')';
        }
        
        function matrix2string(matrix){
            return "matrix(" + [
                matrix.scaleX, matrix.skewX,
                matrix.skewY, matrix.scaleY,
                matrix.moveX, matrix.moveY
            ] + ')';
        }
        
        function transformColor(color, cxform){
            return {
                red: ~~Math.max(0, Math.min((color.red * cxform.multR) + cxform.addR, 255)),
                green: ~~Math.max(0, Math.min((color.green * cxform.multG) + cxform.addG, 255)),
                blue: ~~Math.max(0, Math.min((color.blue * cxform.multB) + cxform.addB, 255)),
                alpha: ~~Math.max(0, Math.min((color.alpha * cxform.multA) + cxform.addA, 255))
            }
        }
        
        function cloneCharacter(character){
            return {
                object: character.object,
                depth: character.depth,
                matrix: character.matrix,
                cxform: character.cxform
            };
        }
        
        function objectId(object){
            var callee = arguments.callee,
                memo = callee._memo || (callee._memo = {}),
                nextId = (callee._nextId || (callee._nextId = 1)),
                key = object2key(object),
                origId = memo[key];
            if(!origId){ memo[key] = nextId; }
            return origId || callee._nextId++;
        }
        
        function object2key(object){
            var a = 1,
                b = 0;
            for(var prop in object){
                var val = object[prop];
                if("object" == typeof val){ a = arguments.callee(val); }
                else{
                    var buff = '' + val;
                    for(var j = 0; buff[j]; j++){
                        a = (a + buff.charCodeAt(j)) % 65521;
                        b = (b + a) % 65521;
                    }
                }
            }
            return (b << 16) | a;
        }
        
        function cloneMatrix(matrix){
            return {
                scaleX: matrix.scaleX, scaleY: matrix.scaleY,
                skewX: matrix.skewX, skewY: matrix.skewY,
                moveX: matrix.moveX, moveY: matrix.moveY
            };
        }
        
        if(doc){
            doc.addEventListener("mousedown", function(e){
                buttonMask |= 0x01 << e.button;
            }, true);
            doc.addEventListener("mouseup", function(e){
                buttonMask ^= 0x01 << e.button;
            }, true);
        }
    })();
    
    /* TODO */
    /*
     * Canvas Renderer
     *
     * @author Cong Liu <cong.liu@intel.com>
     */
    
    (function(){
    // Feature switches
    var USE_WEB_FONT = false;
    
    Gordon.CanvasRenderer = function(width, height, frmSize, quality, scale, bgcolor) {
        var t = this,
            n = t.node = doc.createElement('canvas'),
            ctx = t._ctx = n.getContext('2d');
            t.frmWidth = frmWidth = frmSize.right - frmSize.left,
            t.frmHeight = frmHeight = frmSize.bottom - frmSize.top,
            s = Gordon.scaleValues;
        t.width = n.width = width;
        t.height = n.height = height;
        t.frmSize = frmSize;
        t.quality = quality || Gordon.qualityValues.HIGH;
        t.scale = scale || Gordon.scaleValues.SHOW_ALL;
        switch(t.scale) {
            case s.EXACT_FIT:
                t.scaleX = width / frmWidth;
                t.scaleY = height / frmHeight;
                break;
            case s.SHOW_ALL:
            default:
                t.scaleX = t.scaleY = min(width / frmWidth, height / frmHeight);
                break;
        }
        t.moveX = -frmSize.left + (width - t.scaleX * frmWidth) / 2;
        t.moveY = -frmSize.top + (height - t.scaleY * frmHeight) / 2;
        ctx.lineCap = 'round';
        ctx.lineJoin = 'round';
        t.bgcolor = bgcolor;
        t.setQuality(t.quality);
        if(bgcolor){ t.setBgcolor(bgcolor); }
    
        /* Create stylesheet */
        var cssNode = doc.createElement('style');
        cssNode.type = 'text/css';
        cssNode.rel = 'stylesheet';
        cssNode.media = 'screen';
        cssNode.title = 'dynamicSheet';
        doc.getElementsByTagName("head")[0].appendChild(cssNode);
        t._stylesheet = doc.styleSheets[doc.styleSheets.length - 1];
    
        t._dictionary = {};
        t._timeline = [];
        t._cached = {};
        
        t.init();
    };
    
    Gordon.CanvasRenderer.prototype = {
    		
    	init: function() {
    		var t = this;
    	    t._displayList = {};
    	    t._clipDepth = 0;
    	    t._preserve = false;
    	    
    	    t._context = [];
    	},
    
        setQuality: function(q) {
            // IGNORE
            return this;
        },
    
        setBgcolor: function(rgb) {
            var t = this;
            if(!t.bgcolor){
                t.node.style.background = color2string(rgb);
                t.bgcolor = rgb;
            }
            return t;
        },
    
        define: function(obj) {
            var t = this,
                d = t._dictionary,
                id = obj.id,
                type = obj.type;
    
            d[id] = obj;
            switch(type) {
            case 'font':
            	/* Glyph Fonts */
                var glyphs = obj.glyphs;
    
                if (USE_WEB_FONT) {	// Web Font
                    if(!obj.info) {
                    	var codes = [];
                    	for(var i = 0; i < glyphs.length; i++) codes[i] = i;
                    	obj.info = {
                    		codes: codes,
                    		advanceTable: null,
                    		kerningTable: null,
                    		ascent: 0,
                    		descent: 0
                    	};
                    }
    
                    var info = obj.info,
    	                codes = info.codes;
    	                kerningTable = info.kerningTable,
    	                advanceTable = info.advanceTable;
    
                	var font_svg = '<?xml version="1.0" standalone="yes"?>'+
    	'<!DOCTYPE svg PUBLIC "-//W3C//DTD SVG 1.1//EN" "http://www.w3.org/Graphics/SVG/1.1/DTD/svg11.dtd" >'+
    	'<svg xmlns="http://www.w3.org/2000/svg"><defs>'+
    	'<font horiz-adv-x="'+(advanceTable)+'" >'+
    	'<font-face units-per-em="1024" ascent="'+(info.ascent)+'" descent="'+(info.descent)+'" />';
    	            for(var i = 0, glyph = glyphs[0]; glyph; glyph = glyphs[++i]) {
    	                var cmds = glyph.commands,
    	                    code = codes[i];
    	                if(cmds && code) {
    	                    font_svg += '<glyph unicode="&#x'+code.toString(16)+';" d="'+cmds+'z"/>';
    	                }
    	            }
    	            if(kerningTable) {
    	                for(var i = 0, kern = kerningTable[0]; kern; kern = kerningTable[++i]) {
    	                    font_svg += '<hkern g1="'+kern.code1+'" g2="'+kern.code2+'" k="'+kern.adjustment+'"/>';
    	                }
    	            }
    	            font_svg += '</font>'+
    	'</defs></svg>';
    	            t._stylesheet.insertRule('@font-face {font-family: "f'+id+'"; src: url("data:font/svg;base64,'+btoa(font_svg)+'") format("svg")}', 0);
                }
                break;
            case 'image':
            	var id = objId({'id':obj.id}),
            		colorData = obj.colorData,
    	        	width = obj.width,
            		height = obj.height;
            	if(colorData){
            		var fmt = obj.format;
            		if (fmt == Gordon.bitmapFormats.COLORMAPPED) {
    	                var colorTableSize = obj.colorTableSize || 0,
    	                    bpp = (obj.withAlpha ? 4 : 3),
    	                    cmIdx = colorTableSize * bpp,
    	                    data = (new Gordon.Stream(colorData)).unzip(true),
    	                    withAlpha = obj.withAlpha,
    	                    pxIdx = 0,
    	                    canvas = doc.createElement("canvas"),
    	                    ctx = canvas.getContext("2d"),
    	                    imgData = ctx.createImageData(width, height),
    	                    pxData = imgData.data,
    	                    pad = colorTableSize ? ((width + 3) & ~3) - width : 0;
    	                canvas.width = width;
    	                canvas.height = height;
    	                for(var y = 0; y < height; y++){
    	                    for(var x = 0; x < width; x++){
    	                        var idx = (colorTableSize ? data[cmIdx++] : cmIdx) * bpp,
    	                            alpha = withAlpha ? data[cmIdx + 3] : 255;
    	                        if(alpha){
    	                            pxData[pxIdx] = data[idx];
    	                            pxData[pxIdx + 1] = data[idx + 1];
    	                            pxData[pxIdx + 2] = data[idx + 2];
    	                            pxData[pxIdx + 3] = alpha;
    	                        }
    	                        pxIdx += 4;
    	                    }
    	                    cmIdx += pad;
    	                }
    	                ctx.putImageData(imgData, 0, 0);
    	                t._cached[id] = canvas;
            		} else if(fmt == Gordon.bitmapFormats.RGB15) {
            			// FIXME: not implemented
            			var img = new Image();
            			t._cached[id] = img;
            		} else if(fmt == Gordon.bitmapFormats.RGB24) {
            			var data = (new Gordon.Stream(colorData)).unzip(true),
            				canvas = doc.createElement('canvas'),
            				ctx = canvas.getContext('2d'),
            				imgData = ctx.createImageData(width, height),
            				pxData = imgData.data,
            				pxIdx = idx = 0;
            			canvas.width = width;
            			canvas.height = height;
            			for(var x = 0; x < width; x++) {
            				for(var y = 0; y < height; y++) {
            					pxData[pxIdx] = data[idx + 1];
            					pxData[pxIdx + 1] = data[idx + 2];
            					pxData[pxIdx + 2] = data[idx + 3];
            					pxData[pxIdx + 3] = 255;
            					pxIdx += 4;
            					idx += 4;
            				}
            			}
            			ctx.putImageData(imgData, 0, 0);
            			t._cached[id] = canvas;
            		}
                } else {
    	        	var	alphaData = obj.alphaData,
    	            	uri = "data:image/jpeg;base64," + btoa(obj.data);
    		        if(alphaData){
    		            var img = new Image(),
    		                canvas = doc.createElement("canvas");
    
    		            canvas.width = width;
    		            canvas.height = height;
    		            img.onload = function() {
    		            	var ctx = canvas.getContext("2d"),
    		            		len = width * height,
    		            		data = (new Gordon.Stream(alphaData)).unzip(true);
    		            	ctx.drawImage(img, 0, 0);
    			            var imgData = ctx.getImageData(0, 0, width, height),
    			                pxData = imgData.data,
    			                pxIdx = 0;
    			            for(var i = 0; i < len; i++){
    			                pxData[pxIdx + 3] = data[i];
    			                pxIdx += 4;
    			            }
    			            ctx.putImageData(imgData, 0, 0);
    		            };
    		            img.src = uri;
    		            t._cached[id] = canvas;
    		        } else {
    		        	var img = new Image();
    		        	img.src = uri;
    		        	t._cached[id] = img;
    		        }
            	}
            	break;
            case 'morph':
            	break;
            	// cache diffs
            	var se = obj.startEdges,
        			ee = obj.endEdges,
        			ss = (se instanceof Array ? se : [se]),
        			es = (ee instanceof Array ? ee : [ee]);
            	
            	for(var i = 0; i < ss.length; i++) {
    	    		var sr = ss[i].records,
    	    			er = es[i].records,
    	    			records = [],
    	        		fill = t._diffColor(ss[i].fill[0], ss[i].fill[1]),
    	        		line = {
    	        			width: (ss[i].line.width[1] - ss[i].line.width[0]) / 65535,
    	        			color: t._diffColor(ss[i].line.color[1], ss[i].line.color[0])
    	        		};
    	
    	        	for(var j = 0, length = sr.length; j < length; j++) {
    	        		var ercx = er[j].cx || (er[j].x1 + sr[j].x1) * 0.5,
    	        			ercy = er[j].cy || (er[j].y1 + sr[j].y1) * 0.5,
    	        			srcx = sr[j].cx || (er[j].x1 + sr[j].x1) * 0.5,
    	        			srcy = sr[j].cy || (er[j].y1 + sr[j].y1) * 0.5,
    	        			r = {
    	        			x1: (er[j].x1 - sr[j].x1) / 65535,
    	        			y1: (er[j].y1 - sr[j].y1) / 65535,
    	        			x2: (er[j].x2 - sr[j].x2) / 65535,
    	        			y2: (er[j].y2 - sr[j].y2) / 65535,
    	        			cx: (ercx - srcx) / 65535,
    	        			cy: (ercy - srcy) / 65535
    	        		};
    	        		records.push(r);
    	        	}
    	        	ss[i].diff = {
    	        		fill: fill,
    	        		line: line,
    	        		records: records
    	        	};
            	}
            	break;
            }
            return t;
        },
        
        _diffColor: function(c1, c2) {
        	return {
        		red: (c2.red - c1.red) / 65535,
        		green: (c2.green - c1.green) / 65535,
        		blue: (c2.blue - c1.blue) / 65535,
        		alpha: (c2.alpha - c1.alpha) / 65535
        	};
        },
        _patch: function(obj, diff, ratio) {
        	if(!diff || !ratio) return obj;
        	var dist = {};
        	for(var i in obj) {
        		if(obj.hasOwnProperty(i)) {
        			dist[i] = obj[i] + diff[i] * ratio;
        		}
        	}
        	return dist;
        },
    
        frame: function(frm) {
            var bgcolor = frm.bgcolor,
                t = this;
            if(bgcolor && !t.bgcolor){
                t.setBgcolor(bgcolor);
                t.bgcolor = bgcolor;
            }
            
            t._timeline.push(frm);
            return t;
        },
    
        show: function(frmIdx) {
            var t = this,
                frm = t._timeline[frmIdx],
                d = t._displayList,
                fd = frm ? frm.displayList : {},
                ctx = t._ctx;
            if(!t._preserve) {
    	        ctx.clearRect(0, 0, t.width, t.height);
    	        ctx.save();
    	        ctx.setTransform(t.scaleX, 0, 0, t.scaleY, t.moveX, t.moveY);
            }
    
            t._updateDisplayList(d, fd);
            
            for(var depth in d) {
                var character = d[depth];
                if (character) {
                    t.place(character);
                }
            }
            
            // in case of the last clipped character is removed 
            if (t._clipDepth) {
                t._clipDepth = 0;
                ctx.restore();
            }
            
            if (!t._preserve) {
            	ctx.restore();
            }
            return t;
        },
    
        _updateDisplayList: function(d, fd) {
        	
            for(var depth in fd){
            	var oldChar = d[depth],
            		newChar = fd[depth],
            		update = oldChar && newChar && !newChar.object;
            	
                if (update) { // update character
                    for(var p in newChar) {
                        oldChar[p] = newChar[p];
                    }
                } else {	// replace character
                	d[depth] = oldChar = {};
                    for(var p in newChar) {
                        oldChar[p] = newChar[p];
                    }
                }
            }
            
        },
    
        place: function(character) {
            var t = this,
            	c = t._ctx,
                def = t._dictionary[character.object];
            if (def) {
                if (def.type == 'shape') {
                    t._renderShape(c, def, character);
                } else if (def.type == 'morph') {
                	t._renderMorph(c, def, character);
                } else if (def.type == 'text') {
                    t._renderText(c, def, character);
                } else if (def.type == 'sprite') {
                	t._renderSprite(c, def, character);
                } else {
    /*
                    console.warn(def.type);
                    console.info(def);
    */
                }
            }
            return t;
        },
    
        _renderShape: function(ctx, def, character, morph) {
            var t = this,
                cxform = character.cxform,
                segments = morph ? (def.startEdges instanceof Array ? def.startEdges : [def.startEdges]) : (def.segments || [def]),
                clip = character.clipDepth,
                ratio = character.ratio;
    
            t._prepare(ctx, character);
            for(var j = 0, seg = segments[0]; seg; seg = segments[++j]) {
                var diff = seg.diff || {records: []},
                	records = seg.records,
                    fill = t._patch(seg.fill, diff.fill, ratio),
                    line = t._patch(seg.line, diff.line, ratio);
                ctx.beginPath();
                var firstEdge = t._patch(records[0], diff.records[0], ratio),
                    x1 = 0,
                    y1 = 0,
                    x2 = 0,
                    y2 = 0;
                for(var i = 0, edge = firstEdge; edge; edge = records[++i]){
                	edge = t._patch(edge, diff.records[i], ratio);
                    x1 = edge.x1;
                    y1 = edge.y1;
                    if(x1 != x2 || y1 != y2 || !i){ ctx.moveTo(x1, y1); }
                    x2 = edge.x2;
                    y2 = edge.y2;
                    if(null == edge.cx || null == edge.cy){
                        ctx.lineTo(x2, y2);
                    }else{
                        ctx.quadraticCurveTo(edge.cx, edge.cy, x2, y2);
                    }
                }
        
                if(!line && (x2 != firstEdge.x1 || y2 != firstEdge.y1)){
                    ctx.closePath();
                }
    
                if(!clip) {
                    if (fill) {
                        this._fillShape(ctx, fill, cxform);
                    }
            
                    if (line) {
                        this._strokeShape(ctx, line, cxform);
                    }
                }
            }
            t._postpare(ctx, character);
    
            if(clip) {
                ctx.save();
                ctx.clip();
                t._clipDepth = clip;
            }
    
            if(t._clipDepth && t._clipDepth <= character.depth) {
                ctx.restore();
                t._clipDepth = 0;
            }
        },
        _prepare: function(ctx, character) {
            var m = character.matrix;
            ctx.save();
            if (m) {
                ctx.transform(m.scaleX, m.skewX, m.skewY, m.scaleY, m.moveX, m.moveY);
            }
        },
        _postpare: function(ctx, character) {
            ctx.restore();
        },
        _buildFill: function(ctx, g, cxform) {
            var type = g.type;
            if (type) {
                var fill = ctx.fillStyle;
                switch(type) {
                    case 'linear':
                    case 'radial':
                        var stops = g.stops;
                        if("linear" == type){
                            var gradient = ctx.createLinearGradient(-819.2, 0, 819.2, 0);
                        }else{
                            var gradient = ctx.createRadialGradient(0, 0, 0, 0, 0, 819.2);
                        }
                        for(var i in stops) {
                            var color = stops[i].color;
                            if (cxform) {
                                color = transformColor(color, cxform);
                            }
                            gradient.addColorStop(stops[i].offset, color2string(color));
                        }
                        fill = gradient;
                        break;
                    case 'pattern':
                    	var img = this._cached[objId({'id':g.image.id})];
                        if (cxform) {
                            var id = objId({'id':g.image.id, 'cxform':cxform}),
                                canvas = this._cached[id];
                            if (!canvas) {
                                canvas = doc.createElement('canvas');
                                var ctx2 = canvas.getContext('2d');
                                canvas.width = g.image.width;
                                canvas.height = g.image.height;
                                ctx2.drawImage(img, 0, 0);
                                var data = ctx2.getImageData(0, 0, canvas.width, canvas.height);
                                transformColorArray(data.data, cxform);
                                ctx2.putImageData(data, 0, 0);
                                this._cached[id] = canvas;
                            }
                            img = canvas;
                        }
    /*
                        console.info(g.image.id);
                        console.info(g.matrix);
    */
                       
                        fill = ctx.createPattern(img, g.repeat ? 'repeat':'no-repeat');
                    	break;
                }
                return fill;
            } else {
                if (cxform) {
                    g = transformColor(g, cxform);
                }
                return color2string(g);
            }
        },
        _fillShape: function(ctx, fill, cxform) {
            var m = fill.matrix;
            ctx.save();
            if (m) {
                ctx.transform(m.scaleX, m.skewX, m.skewY, m.scaleY, m.moveX, m.moveY);
            }
            ctx.fillStyle = this._buildFill(ctx, fill, cxform);
            ctx.fill();
            ctx.restore();
        },
        _strokeShape: function(ctx, stroke, cxform) {
            var t = this,
                m = stroke.matrix;
            ctx.save();
            if (m) {
                ctx.transform(m.scaleX, m.skewY, m.skewX, m.scaleY, m.moveX, m.moveY);
            }
            ctx.strokeStyle = t._buildFill(ctx, stroke.color, cxform);
            ctx.lineWidth = min(stroke.width, 20);
            ctx.stroke();
            ctx.restore();
        },
        _renderMorph: function(ctx, def, character) {
    //        console.info(character.ratio);
            this._renderShape(ctx, def, character, true);
        },
        _renderText: function(ctx, def, character) {
            var t = this,
                c = ctx,
                d = def,
                o = character,
                strings = def.strings;
    
            t._prepare(c, o);
            for(var i = 0, string = strings[0]; string; string = strings[++i]) {
            	if(USE_WEB_FONT) {
            		t._renderString(c, string);
            	} else {
            		t._renderStringStd(c, string);
            	}
            }
            t._postpare(c, o);
        },
        _renderString: function(ctx, string) {
            var t = this,
                c = ctx,
                entries = string.entries,
                fill = string.fill,
                font = t._dictionary[string.font],
                glyphs = font.glyphs,
                info = font.info,
                codes = info ? info.codes : null,
                x = string.x, y = string.y;
            t._prepare(c, string);
            if (!info) {
            	console.warn('no font info found');
            	console.info(font);
            }
            for(var j = 0, entry = entries[0]; entry; entry = entries[++j]) {
                var str = String.fromCharCode(codes ? codes[entry.index] : entry.index);
                if(' ' != str || str.length) {
                    c.font = string.size + 'px f' + font.id;
                    if(fill) {
                        c.fillStyle = t._buildFill(c, fill, null);
                    }
                    c.fillText(str, x, y);
                }
                x += entry.advance;
            }
            t._postpare(c, string);
        },
        _renderStringStd: function(ctx, string) {
        	var t = this,
        		c = ctx,
        		entries = string.entries,
        		fill = string.fill,
        		font = t._dictionary[string.font],
        		scale = string.size / (font.extended ? 1024 * 20: 1024),
        		glyphs = font.glyphs,
        		info = font.info,
                x = string.x, y = string.y;
        	
        	for(var j = 0, entry = entries[0]; entry; entry = entries[++j]) {
        		var index = entry.index,
        			g = glyphs[index],
        			paths = g.paths;
        		c.save();
        		c.translate(x, y);
        		c.scale(scale, scale);
        		c.beginPath();
        		for(var i = 0, path = paths[0]; path; path = paths[++i]) {
        			switch(path.type) {
        			case 'M':
        				c.moveTo(path.x, path.y);
        				break;
        			case 'L':
        			case 'V':
        			case 'H':
        				c.lineTo(path.x, path.y);
        				break;
        			case 'Q':
        				c.quadraticCurveTo(path.cx, path.cy, path.x, path.y);
        				break;
        			}
        		}
        		c.closePath();
        		if(fill) {
        			c.fillStyle = t._buildFill(c, fill, null);
            		c.fill();
        		}
        		c.restore();
        		x += entry.advance;
        	}
        },
    	
    	_contextKeys: ['_timeline', '_displayList', '_clipDepth', '_preserve'],
    	
    	saveContext: function(newContext) {
    		var t = this,
    			context = {};
    		for(var i in t._contextKeys) {
    			var key = t._contextKeys[i];
    			context[key] = t[key];
    			t[key] = newContext[key];
    		}
    		t._context.push(context);
    	},
    	
    	restoreContext: function() {
    		var t = this,
    			context = t._context.pop();
    		for(var i in t._contextKeys) {
    			t[i] = context[t._contextKeys[i]];
    		}
    	},
    	
    	_renderSprite: function(ctx, def, sprite) {
    		if(!sprite.context) {
    			sprite.context = {
    				_timeline: def.timeline,
    				_displayList: {},
    				_clipDepth: 0,
    				_preserve: true
    			};
    			sprite.frmIdx = 0;
    		}
    		var m = sprite.matrix;
        	this.saveContext(sprite.context);
        	ctx.save();
        	if (m) {
        		ctx.transform(m.scaleX, m.skewX, m.skewY, m.scaleY, m.moveX, m.moveY);
        	}
        	this.show(sprite.frmIdx++);
        	ctx.restore();
        	this.restoreContext();
        }
    };
    
    var REGEXP_IS_COLOR = /^([\da-f]{1,2}){3}$/i;
    
    function color2string(color){
        if("string" == typeof color){ return REGEXP_IS_COLOR.test(color) ? color : null; }
        if (color.alpha == undefined) {
            return "rgb(" + [color.red, color.green, color.blue] + ')';
        } else {
            return "rgba(" + [color.red, color.green, color.blue, color.alpha / 255] + ')';
        }
    }
    
    function transformColor(color, cxform){
        return {
            red: ~~max(0, min((color.red * cxform.multR) + cxform.addR, 255)),
            green: ~~max(0, min((color.green * cxform.multG) + cxform.addG, 255)),
            blue: ~~max(0, min((color.blue * cxform.multB) + cxform.addB, 255)),
            alpha: ~~max(0, min(((color.alpha == undefined ? 255: color.alpha) * cxform.multA) + cxform.addA, 255))
        };
    }
    
    function transformColorArray(colorArray, cxform){
    	var multR = cxform.multR, multG = cxform.multG, multB = cxform.multB, multA = cxform.multA,
    		addR = cxform.addR, addG = cxform.addG, addB = cxform.addB, addA = cxform.addA;
    	for(var i = 0, length = colorArray.length; i < length; i += 4) {
    		colorArray[i] = ~~max(0, min((colorArray[i] * multR) + addR, 255));
    		colorArray[i + 1] = ~~max(0, min((colorArray[i + 1] * multG) + addG, 255));
    		colorArray[i + 2] = ~~max(0, min((colorArray[i + 2] * multB) + addB, 255));
    		colorArray[i + 3] = ~~max(0, min((colorArray[i + 3] * multA) + addA, 255));
    	}
    
    	return colorArray;
    }
    
    function transformPoint(matrix, p) {
        return [matrix.scaleX * p[0] + matrix.skewX * p[1] + matrix.moveX, matrix.skewY * p[0] + matrix.scaleY * p[1] + matrix.moveY];
    }
    
    function objId(obj) {
        return JSON.stringify(obj);
    }
    
    })();
    
    win.Gordon = Gordon;
})(self);
