"""
A Python array is as lean as a C array.
E.g. an array of float values does not hold float instances, 
but the bytes representing their machine values similar to an array of double in C

When creating an array, provide a typecode, a letter to determine
the underlying C type used to store each item in the array

e.g.  For example, b is the typecode for what C calls a signed char, 
an integer ranging from –128 to 127. If you create an array('b'), 
then each item will be stored in a single byte and interpreted as an integer.


>>> from array import array  
>>> from random import random
>>> floats = array('d', (random() for i in range(10**7)))  # create array of double-precision floats using a generator expression *note tuple syntax creates items one by one without memory
>>> fp = open('floats.bin', 'wb') #  write to binary file named floats.bin
>>> floats.tofile(fp)  #4 save array as binary file
>>> fp.close()
>>> floats2 = array('d')  # create empty array
>>> fp = open('floats.bin', 'rb') # read in binary file named floats.bin 
>>> floats2.fromfile(fp, 10**7)  # read 10 million numbers from the binary file
>>> fp.close()
>>> floats2 == floats  # contents match
True


It takes 0.1s for array.fromfile to load 10M floats from a binary file created with array.tofile
That's 60 times faster than reading teh numbers from a text file
Saving with array.tofile is about 7 times faster than writing one folat per line in a text file
In addition, the size of the binary file with 10 million doubles is 80,000,000 bytes (8 bytes per double, zero overhead), 
while the text file has 181,515,739 bytes, for the same data.

As of Python 3.10, the array type does not have an in-place sort method like list.sort(). If you need to sort an array, use the built-in sorted function to rebuild the array:
a = array.array(a.typecode, sorted(a))

"""


if __name__ == "__main__":
    import doctest
    doctest.testmod()

