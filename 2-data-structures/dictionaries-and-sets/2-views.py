"""
The dict instance methods .keys(), .values(), and .items() return instances of classes called dict_keys, dict_values, and dict_items, respectively. These dictionary views are read-only projections of the internal data structures used in the dict implementation.

views—which allow high-performance operations on a dict, without unnecessary copying of data.
A view object is a dynamic proxy. If the source dict is updated, you can immediately see the changes through an existing view.

>>> d = dict(a=10, b=20, c=30)
>>> values = d.values()
>>> values
dict_values([10, 20, 30])
>>> len(values)  
3
>>> list(values)  
[10, 20, 30]

# >>> reversed(values)  
# <dict_reversevalueiterator object at 0x10e9e7310>
>>> values[0] 
Traceback (most recent call last):
  File "<stdin>", line 1, in <module>
TypeError: 'dict_values' object is not subscriptable

>>> d['z'] = 99
>>> d
{'a': 10, 'b': 20, 'c': 30, 'z': 99}
>>> values
dict_values([10, 20, 30, 99])

"""


if __name__ == "__main__":
    import doctest
    doctest.testmod()
