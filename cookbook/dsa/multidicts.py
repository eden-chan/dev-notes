"""
make a dictionary that maps keys to more than one value (a so-called “multidict”).

>>> d = {}

>>> pairs = [('a',1),('b',2),('c',3)]
>>> for key, value in pairs:
...    if key not in d:
...         d[key] = []
...    d[key].append(value)

>>> d 
{'a': [1], 'b': [2], 'c': [3]}


>>> d = defaultdict(list)
>>> for key, value in pairs:
...     d[key].append(value)
>>> d 
{'a': [1], 'b': [2], 'c': [3]}

"""

if __name__ == "__main__":
    import doctest
    doctest.testmod()

