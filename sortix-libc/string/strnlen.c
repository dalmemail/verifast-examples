/*
 * Copyright (c) 2011, 2012 Jonas 'Sortie' Termansen.
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 * string/strnlen.c
 * Returns the length of a fixed length string.
 */

#include <string.h>

size_t strnlen(const char* str, size_t maxlen)
    //@ requires [?f]chars(str, maxlen, ?cs);
    //@ ensures [f]chars(str, maxlen, cs) &*& result <= maxlen &*& (result < maxlen) ? mem('\0', cs) == true &*& result == index_of('\0', cs) : true;
{
	size_t ret = 0;
	while (ret < maxlen)
	    //@ requires [f]chars(str + ret, maxlen - ret, ?cs_aux);
	    //@ ensures [f]chars(str + old_ret, maxlen - old_ret, cs_aux) &*& (ret < maxlen) ? mem('\0', cs_aux) == true &*& ret - old_ret == index_of('\0', cs_aux) : true;
	{
	    // can't do auto-open since we're not consuming a predicate assertion
	    //@ open [f]chars(_, _, _);
	    if (!str[ret])
	        // auto-close !
	        break;

		ret++;
	    //@ recursive_call();
	    // auto-close !
	    // close [f]chars(str + old_ret, maxlen - old_ret, cs_aux);
	}
	return ret;
}
