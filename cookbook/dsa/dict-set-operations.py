"""

Problem
You have two dictionaries and want to find out what they might have in common
(same keys, same values, etc.).

>>> a = {
...    'x' : 1,
...    'y' : 2,
...    'z' : 3
... }

>>> b = {
...    'w' : 10,
...    'x' : 11,
...   'y' : 2
... }

>>> a.keys() & b.keys()
{'y', 'x'}
>>> a.keys() - b.keys()
{'z'}
>>> a.items() & b.items() 
{('y', 2)}

Make a new dictionary with certain keys removed
>>> c = {key:a[key] for key in a.keys() - {'z', 'w'}}
>>> c 
{'y': 2, 'x': 1}


"""

if __name__ == "__main__":
    import doctest
    doctest.testmod()
    