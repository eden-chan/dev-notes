# Tuples as Immutable Lists
# Clarity: when you see a tuple in code, you know its length will never change.
# Performance: a tuple uses less memory than a list of the same length, and they allow Python to do some optimizations.
# Note: contents of tuple is immutable, but that only means the references held by the tuple
# will always point to the same objects. Thus if one reference points to a mutable content, the content can change.

"""
>>> a = (10, 'alpha', [1, 2])
>>> b = (10, 'alpha', [1, 2])
>>> a == b
True
>>> b[-1].append(99)
>>> a == b
False
>>> b
(10, 'alpha', [1, 2, 99])
"""

# Unpacking 

# Parallel assignment 
"""
>>> ab = (1, 2)
>>> a,b = ab
>>> a
1
>>> b
>>> b, a = a, b
"""

# Using * to grab excess items
"""
>>> a, b, *rest = range(5)
>>> a, b, rest
(0, 1, [2, 3, 4])
>>> a, b, *rest = range(3)
>>> a, b, rest
(0, 1, [2])
>>> a, b, *rest = range(2)
>>> a, b, rest
(0, 1, [])
"""
if __name__ == "__main__":
    import doctest
    doctest.testmod()
