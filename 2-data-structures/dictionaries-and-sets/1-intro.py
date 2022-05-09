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
Ice cream details: {'flavor': 'vanilla', 'cost': 199}

>>> from collections import abc
>>> my_dict = {}
>>> isinstance(my_dict, abc.Mapping)
True
>>> isinstance(my_dict, abc.MutableMapping)
True

my_dict.setdefault(key, []).append(new_value)
# 1 lookup 
if key not in my_dict:
    my_dict[key] = []
my_dict[key].append(new_value)
# 3 lookups

A ChainMap instance holds a list of mappings that can be searched as one.
 The lookup is performed on each input mapping in the order it appears 
 in the constructor call, and succeeds as soon as the key is found in 
 one of those mappings. For example:

>>> d1 = dict(a=1, b=3)
>>> d2 = dict(a=2, b=4, c=6)
>>> from collections import ChainMap
>>> chain = ChainMap(d1, d2)
>>> chain['a']
1
>>> chain['c']
6

The ChainMap instance does not copy the input mappings,
 but holds references to them. Updates or insertions to a
  ChainMap only affect the first input mapping. 
>>> chain['c'] = -1
>>> d1
{'a': 1, 'b': 3, 'c': -1}
>>> d2
{'a': 2, 'b': 4, 'c': 6}


A mapping that holds an integer count for each key.
 Updating an existing key adds to its count. 
>>> import collections
>>> ct = collections.Counter('abracadabra')
>>> ct
Counter({'a': 5, 'b': 2, 'r': 2, 'c': 1, 'd': 1})
>>> ct.update('aaaaazzz')
>>> ct
Counter({'a': 10, 'z': 3, 'b': 2, 'r': 2, 'c': 1, 'd': 1})
>>> ct.most_common(3)
[('a', 10), ('z', 3), ('b', 2)]

Note that the 'b' and 'r' keys are tied in third place, but ct.most_common(3) shows only three counts.

To use collections.Counter as a multiset, 
pretend each key is an element in the set, 
and the count is the number of occurrences of that element in the set.

# Read only instance from dict
>>> from types import MappingProxyType
>>> d = {1: 'A'}
>>> d_proxy = MappingProxyType(d)
>>> d_proxy
mappingproxy({1: 'A'})
>>> d_proxy[1]
'A'
>>> d_proxy[2] = 'x'  
Traceback (most recent call last):
  File "<stdin>", line 1, in <module>
TypeError: 'mappingproxy' object does not support item assignment
>>> d[2] = 'B'
>>> d_proxy  
mappingproxy({1: 'A', 2: 'B'})
>>> d_proxy[2]
'B'

"""


if __name__ == "__main__":
    import doctest
    doctest.testmod()
