# TO LEARN: 
# List comprehensions and the basics of generator expressions;
# Using tuples as records, versus using tuples as immutable lists;
# Sequence unpacking and sequence patterns;
# Reading from slices and writing to slices;
# Specialized sequence types, like arrays and queues.

# The standard library offers a rich selection of sequence types implemented in C:

# Container sequences
# Can hold items of different types, including nested containers. Some examples: list, tuple, and collections.deque.

# Flat sequences
# Hold items of one simple type. Some examples: str, bytes, and array.array.

# A container sequence holds references to the objects it contains, 
# which may be of any type, while a flat sequence stores the value of its contents 
# in its own memory space, and not as distinct Python objects.

# Thus flat sequences are more compact, but are limited to holding primitive machine values like bytes, integers, and floats
# Every Python object in memory has a header with metadata. The simplest Python object, a float, has a value field and two metadata fields:
# ob_refcnt: the object’s reference count;
# ob_type: a pointer to the object’s type;
# ob_fval: a C double holding the value of the float.

# That’s why an array of floats is much more compact than a tuple of floats: the array is a single object holding the raw values of the floats, while the tuple consists of several objects—the tuple itself and each float object contained in it.

# Another way of grouping sequence types is by mutability:
# Mutable sequences
# E.g. list, bytearray, array.array, and collections.deque.

# Immutable sequences
# E.g. tuple, str, and bytes.
# mutable sequences inherit all methods from immutable sequences, and 
# implement several additional methods.
# built-in concrete sequence types don't subclass the Sequence and MutableSequence ABCs
# but are virtual subclasses registered with those ABCs
"""
>>> from collections import abc
>>> issubclass(tuple, abc.Sequence)
True
>>> issubclass(list, abc.MutableSequence)
True
"""

if __name__ == "__main__":
    import doctest
    doctest.testmod()
