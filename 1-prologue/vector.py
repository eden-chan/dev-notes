"""
Implement special methods for Vector arithmetic

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

    def __init__(self, x=0,y=0):
        self.x=x
        self.y=y
    
    def __repr__(self):
        #  replacement_field ::=  "{" [field_name] ["!" conversion] [":" format_spec] "}"
        # The conversion field causes a type coercion before formatting, where !r in
        #  {self.x!r}" tells the intepreter to call repr() on the argument first
        # https://docs.python.org/2/library/string.html#format-string-syntax

        return f'Vector({self.x!r}, {self.y!r})'

    def __abs__(self):
        return math.hypot(self.x, self.y)

    def __bool__(self):
        return bool(abs(self))

    def __add__(self, other):
        x = self.x + other.x
        y = self.y + other.y
        return Vector(x, y)

    def __mul__(self, scalar):
        x = self.x * scalar
        y = self.y * scalar 
        return Vector(x, y)



if __name__ == "__main__":
    import doctest
    doctest.testmod()
