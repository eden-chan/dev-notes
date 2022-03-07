# A common feature of list, tuple, str, and all sequence types in Python is the support of slicing operations, which are more powerful than most people realize.
# length of a slice or range when only the stop position is given: range(3) and my_list[:3] both produce three items.
"""
>>> len(range(3))
3
>>> my_list = ['a', 'b', 'c', 'd', 'e', 'f']
>>> len(my_list[:3])
3

# length of a slice or range when start and stop are given: just subtract stop - start.
>>> len(range(4,9))
5
>>> len(my_list[1:6])
5

# split a sequence in two parts at any index x, without overlapping: simply get my_list[:x] and my_list[x:]. For example
>>> l = [10, 20, 30, 40, 50, 60]
>>> l[:2]  # split at 2
[10, 20]
>>> l[2:]
[30, 40, 50, 60]
>>> l[:3]  # split at 3
[10, 20, 30]
>>> l[3:]
[40, 50, 60]


# Slice objects
>>> s = 'bicycle'
>>> s[::3]
'bye'
>>> s[::-1]
'elcycib'
>>> s[::-2]
'eccb'

# Assigning to Slices
>>> l = list(range(10))
>>> l
[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
>>> l[2:5] = [20, 30]
>>> l
[0, 1, 20, 30, 5, 6, 7, 8, 9]
>>> del l[5:7]
>>> l
[0, 1, 20, 30, 5, 8, 9]
>>> l[3::2] = [11, 22]
>>> l
[0, 1, 20, 11, 5, 22, 9]
>>> l[2:5] = 100  #1
Traceback (most recent call last):
  File "<stdin>", line 1, in <module>
TypeError: can only assign an iterable
>>> l[2:5] = [100]
>>> l
[0, 1, 100, 22, 9]

#1) When the target of the assignment is a slice, the right-hand side must be an iterable object, even if it has just one item.
"""

if __name__ == "__main__":
    import doctest
    doctest.testmod()
