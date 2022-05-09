"""
A set is a collection of unique objects. A basic use case is removing duplication:
https://docs.python.org/3/library/collections.html

The order of the output changes for each Python process,
 because of the salted hash algorithm:

 The hash code of an object may be different depending on the version of 
 Python, the machine architecture, and because of a salt added to the hash 
 computation for security reasons.
 The hash code of a correctly implemented object is guaranteed to be 
 constant only within one Python process.

>>> l = ['spam', 'spam', 'eggs', 'spam', 'bacon', 'eggs']
# >>> set(l)
# {'spam', 'eggs', 'bacon'}
# >>> list(set(l))
# ['spam', 'eggs', 'bacon']


# If you want to remove duplicates but also preserve 
# the order of the first occurrence of each item,
#  you can now use a plain dict to do it, like this:
>>> dict.fromkeys(l).keys()
dict_keys(['spam', 'eggs', 'bacon'])
>>> list(dict.fromkeys(l).keys())
['spam', 'eggs', 'bacon']


Set elements must be hashable. 
The set type is not hashable, so you can’t build a set with nested set 
instances. But frozenset is hashable, so you can have frozenset elements 
inside a set.


Smart use of set operations can reduce both the line count and the
 execution time of Python programs, at the same time making code easier 
to read and reason about—by removing loops and conditional logic.

found = len(needles & haystack) 
# set is faster, but requires set

found = 0
for n in needles:
    if n in haystack:
        found += 1

# iteratable can work on iterables, not just sets.

# Build sets on the fly
there is an extra cost involved in building the sets ,
 but if either the needles or the haystack is already a set,
 these alternatives can be cheaper:

found = len(set(needles) & set(haystack))
# another way:
found = len(set(needles).intersection(haystack)) 

Any one of the preceding examples are capable of searching 1,000 elements
 in a haystack of 10,000,000 items in about 0.3 milliseconds—that’s 
 close to 0.3 microseconds per element.
Besides the extremely fast membership test 
(thanks to the underlying hash table), the set and frozenset built-in types 
provide a rich API to create new sets or, in the case of set, to change existing ones.

Don’t forget that to create an empty set, you should use the 
constructor without an argument: set(). If you write {}, 
you’re creating an empty dict—this hasn’t changed in Python 3.
>>> type({})
<class 'dict'>
>>> s = {1}
>>> type(s)
<class 'set'>
>>> s
{1}
>>> s.pop()
1
>>> s
set()

Literal set syntax like {1, 2, 3} is both faster and more 
readable than calling the constructor (e.g., set([1, 2, 3])). 
The latter form is slower because, to evaluate it, 
Python has to look up the set name to fetch the constructor, 
then build a list, and finally pass it to the constructor.

There is no special syntax to represent frozenset literals
—they must be created by calling the constructor.
>>> frozenset(range(10))
frozenset({0, 1, 2, 3, 4, 5, 6, 7, 8, 9})

# >>> from unicodedata import name  
# >>> {chr(i) for i in range(32, 256) if 'SIGN' in name(chr(i),'')}  
# {'§', '=', '¢', '#', '¤', '<', '¥', 'µ', '×', '$', '¶', '£', '©',
# '°', '+', '÷', '±', '>', '¬', '®', '%'}

The infix operators require that both operands be sets, 
but all other methods take one or more iterable arguments. 
For example, to produce the union of four collections, a, b, c, and d,
 you can call a.union(b, c, d),
  where a must be a set, but b, c, and d can be iterables of any type
   that produce hashable items. 
   If you need to create a new set with the union of four iterables, 
   instead of updating an existing set, you can write {*a, *b, *c, *d}

Set Operations on Dict views
>>> d1 = dict(a=1, b=2, c=3, d=4)
>>> d2 = dict(b=20, d=40, e=50)
>>> d1.keys() & d2.keys()
{'b', 'd'}

Note that the return value of & is a set. 
Even better: the set operators in dictionary views are 
compatible with set instances. Check this out:

>>> s = {'a', 'e', 'i'}
>>> d1.keys() & s
{'a'}
>>> d1.keys() | s
{'a', 'c', 'b', 'd', 'i', 'e'}

A dict_items view only works as a set if all values in the dict are hashable.
Attempting set operations on a dict_items view with an unhashable value raises
 TypeError: unhashable type 'T', with T as the type of the offending value.
On the other hand, a dict_keys view can always be used as a set, because every key is hashable—by definition.

"""

if __name__ == "__main__":
    import doctest
    doctest.testmod()

