"""
This is the "example" module.

The example module supplies one function, factorial().  For example,

>>> v1 = Vector(2, 4)
>>> v2 = Vector(2, 1)
>>> v1 + v2
Vector(4, 5)


# abs is a built-in function returns the absolute value of integers and floats, 
# and magnitude of complex numbers. To be consistent, our API will use abs to 
# return the magnitude of a vector
>>> v = Vector(3, 4)
>>> abs(v)
5.0

# Scalar multiplication
>>> v * 3
Vector(9, 12)
>>> abs(v * 3)
15.0

# Vector class implementing the operations just described, through the use of the special methods __repr__, __abs__, __add__ and __mul__.
"""
import math 

class Vector: 
    ...


if __name__ == "__main__":
    import doctest
    doctest.testmod()
