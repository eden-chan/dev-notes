"""
A memoryview is a NumPy array in Python (without the math). 
It lets you to share memory between data-structures 
(things like PIL images, SQLite databases, 
NumPy arrays, etc.) without first copying. 
This is performant for large data sets.

>>> from array import array
>>> octets = array('B', range(6)) # build array of 6 bytes
>>> m1 = memoryview(octets) # make a memoryview out of said array
>>> m1.tolist() # export it as list
[0, 1, 2, 3, 4, 5]
>>> m2 = m1.cast('B', [2, 3]) # create a second memoryview out of octets
>>> m2.tolist()
[[0, 1, 2], [3, 4, 5]]
>>> m3 = m1.cast('B', [3, 2]) create a third memory view out of octets
>>> m3.tolist()
[[0, 1], [2, 3], [4, 5]]
>>> m2[1,1] = 22
>>> m3[1,1] = 33
>>> octets # show that memory is being referenced, and not copied
array('B', [0, 1, 2, 33, 22, 5]) 
"""

if __name__ == "__main__":
    import doctest
    doctest.testmod()