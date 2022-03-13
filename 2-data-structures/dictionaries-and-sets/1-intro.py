"""
Python is basically dicts wrapped in loads of syntactic sugar.
Here is a brief outline of this chapter:

Modern syntax to build and handle dicts and mappings, including enhanced unpacking and pattern matching.

Common methods of mapping types.

Special handling for missing keys.

Variations of dict in the standard library.

The set and frozenset types.

Implications of hash tables in the behavior of sets and dictionaries.


Dict Comprehensions
>>> dial_codes = [                                                  
...     (880, 'Bangladesh'),
...     (55,  'Brazil'),
...     (86,  'China'),
...     (91,  'India'),
...     (62,  'Indonesia'),
...     (81,  'Japan'),
...     (234, 'Nigeria'),
...     (92,  'Pakistan'),
...     (7,   'Russia'),
...     (1,   'United States'),
... ]
>>> country_dial = { country : code for code, country in dial_codes }
>>> country_dial
{'Bangladesh': 880, 'Brazil': 55, 'China': 86, 'India': 91, 'Indonesia': 62, 'Japan': 81, 'Nigeria': 234, 'Pakistan': 92, 'Russia': 7, 'United States': 1}
>>> {code: country.upper()                                          
...     for country, code in sorted(country_dial.items())
...     if code < 70}
{55: 'BRAZIL', 62: 'INDONESIA', 7: 'RUSSIA', 1: 'UNITED STATES'}

Unpacking Mappings
In functions, there can't be duplicate key-word arguments
>>> def dump(**kwargs):
...     return kwargs
>>> dump(**{'x': 1}, y=2, **{'z': 3})
{'x': 1, 'y': 2, 'z': 3}


In literals, duplicate keys are allowed, taking the latest occurcence
>>> {'a': 0, **{'x': 1}, 'y': 2, **{'z': 3, 'x': 4}}
{'a': 0, 'x': 4, 'y': 2, 'z': 3}

Merge Mappings with | and |=
>>> d1 = {'a': 1, 'b': 3}
>>> d2 = {'a': 2, 'b': 4, 'c': 6}
>>> d1 | d2
{'a': 2, 'b': 4, 'c': 6}

To update an existing mapping in-place, use |=
>>> d1
{'a': 1, 'b': 3}
>>> d1 |= d2
>>> d1
{'a': 2, 'b': 4, 'c': 6}


Pattern Matching 😊 with **extra must be the last argument in the pattern
>>> food = dict(category='ice cream', flavor='vanilla', cost=199)
>>> match food:
...     case {'category': 'ice cream', **details}:
...         print(f'Ice cream details: {details}')
...
Ice cream details: {'flavor': 'vanilla', 'cost': 199}

>>> from collections import abc
>>> my_dict = {}
>>> isinstance(my_dict, abc.Mapping)
True
>>> isinstance(my_dict, abc.MutableMapping)
True
"""

if __name__ == "__main__":
    import doctest
    doctest.testmod()
