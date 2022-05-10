"""
The concept of “string” is simple enough: a string is a sequence of characters. The problem lies in the definition of “character.”

In 2021, the best definition of “character” we have is a Unicode character.
The Unicode standard explicitly separates the identity of characters from specific byte representations:

The identity of a character—its code point—is a number from 0 to 1,114,111 
(base 10), shown in the Unicode standard as 4 to 6 hex digits with a 
“U+” prefix, from U+0000 to U+10FFFF. For example,
 the code point for the letter A is U+0041, the Euro sign is U+20AC

 The actual bytes that represent a character depend on the encoding in use. 
 An encoding is an algorithm that converts code points to byte sequences 
 and vice versa. The code point for the letter A (U+0041) 
 is encoded as the single byte \x41 in the UTF-8 encoding, or 
 as the bytes \x41\x00 in UTF-16LE encoding.

>>> s = 'café'
>>> len(s)  
4
>>> b = s.encode('utf8')  
>>> b 
b'caf\xc3\xa9'  
>>> len(b)  
5
>>> b.decode('utf8')  
'café'


Python 3 str is pretty much the Python 2 unicode type with a new name,
 the Python 3 bytes is not simply the old str renamed, and there is 
 also the closely related bytearray type. 
Each item in bytes or bytearray is an integer from 0 to 255, 
and not a one-character string like in the Python 2 str. 
However, a slice of a binary sequence always produces a binary sequence 
of the same type—including slices of length 1

>>> cafe = bytes('café', encoding='utf_8')  
>>> cafe
b'caf\xc3\xa9'
>>> cafe[0]  
99
>>> cafe[:1]  
b'c'
>>> cafe_arr = bytearray(cafe)
>>> cafe_arr  
bytearray(b'caf\xc3\xa9')
>>> cafe_arr[-1:]  
bytearray(b'\xa9')

The fact that my_bytes[0] retrieves an int but my_bytes[:1] returns a bytes sequence of length 1 is only surprising because we are used to Python’s str type, where s[0] == s[:1]. For all other sequence types in Python, 1 item is not the same as a slice of length 1.

Although binary sequences are really sequences of integers, their literal 
notation reflects the fact that ASCII text is often embedded in them.
 Therefore, four different displays are used, depending on each byte value:

For bytes with decimal codes 32 to 126—from space to ~ (tilde)—
the ASCII character itself is used.

For bytes corresponding to tab, newline, carriage return, and \, 
the escape sequences \t, \n, \r, and \\ are used.

If both string delimiters ' and " appear in the byte sequence, 
the whole sequence is delimited by ', and any ' inside are escaped as \'.3

For other byte values, a hexadecimal escape sequence is used
 (e.g., \x00 is the null byte).

Both bytes and bytearray support every str method except those that 
do formatting (format, format_map) and those that depend on Unicode data
This means that you can use familiar string methods like endswith, 
replace, strip, translate, upper, and dozens of others
 with binary sequences—only using bytes and not str arguments.


utf-8 > 97.7%
The most common 8-bit encoding on the web, by far, as of July 2021, “W3Techs: Usage statistics of character encodings for websites” 
claims that 97% of sites use UTF-8, up from 81.4% when I wrote this paragraph
in the first edition of this book in September 2014.

utf-16le - < 0.1%
One form of the UTF 16-bit encoding scheme; all UTF-16 encodings support code points beyond U+FFFF through escape sequences called “surrogate pairs.”
As of 2021, more than 57% of the allocated code points are above U+FFFF, including the all-important emojis.



The best practice for handling text I/O is the “Unicode sandwich” 
This means that bytes should be decoded to str as early as possible on input 
(e.g., when opening a file for reading). 
The “filling” of the sandwich is the business logic of your program, 
where text handling is done exclusively on str objects. 
You should never be encoding or decoding in the middle of other processing. 
On output, the str are encoded to bytes as late as possible. 
Most web frameworks work like that, and we rarely touch bytes when using them. 
In Django, for example, your views should output Unicode str; 
Django itself takes care of encoding the response to bytes, 
using UTF-8 by default.

Code that has to run on multiple machines or on multiple occasions 
should never depend on encoding defaults.
 Always pass an explicit encoding= argument when opening text files, 
 because the default may change from one machine to the next, 
 or from one day to the next

Normalizing Unicode for Reliable Comparisons

Unicode standard, sequences like 'é' and 'e\u0301' are called 
“canonical equivalents,” and applications are supposed to treat
 them as the same. But Python sees two different sequences of code points,
and considers them not equal.

>>> s1 = 'café'
>>> s2 = 'cafe\N{COMBINING ACUTE ACCENT}'
>>> s1, s2
('café', 'café')
>>> len(s1), len(s2)
(4, 5)
>>> s1 == s2
False

The solution is unicodedata.normalize(). 
The first argument to that function is one of four strings: 
'NFC', 'NFD', 'NFKC', and 'NFKD'. 

Normalization Form C (NFC) composes the code points to 
produce the shortest equivalent string, while NFD decomposes, 
expanding composed characters into base characters and separate
 combining characters. B


>>> from unicodedata import normalize
>>> s1 = 'café'
>>> s2 = 'cafe\N{COMBINING ACUTE ACCENT}'
>>> len(s1), len(s2)
(4, 5)
>>> len(normalize('NFC', s1)), len(normalize('NFC', s2))
(4, 4)
>>> len(normalize('NFD', s1)), len(normalize('NFD', s2))
(5, 5)
>>> normalize('NFC', s1) == normalize('NFC', s2)
True
>>> normalize('NFD', s1) == normalize('NFD', s2)
True


NFKC and NFKD normalization cause data loss and should be applied 
only in special cases like search and indexing, 
and not for permanent storage of text.

Case folding is essentially converting all text to lowercase, 
with some additional transformations. It is supported by the str.casefold() method.

As we’ve seen, NFC and NFD are safe to use and allow sensible 
comparisons between Unicode strings. 
NFC is the best normalized form for most applications. 
str.casefold() is the way to go for case-insensitive comparisons.


Python sorts sequences of any type by comparing the items in
 each sequence one by one. For strings, this means comparing the code points.
  Unfortunately, this produces unacceptable results for anyone who uses 
  non-ASCII characters.
>>> fruits = ['caju', 'atemoia', 'cajá', 'açaí', 'acerola']
>>> sorted(fruits)
['acerola', 'atemoia', 'açaí', 'caju', 'cajá']
"""

if __name__ == "__main__":
    import doctest
    doctest.testmod()
