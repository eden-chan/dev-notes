"""
The list.sort method sorts a list in-place—that is, without making a copy. 
It returns None to remind us that it changes the receiver
and does not create a new list.
This is an important Python API convention: functions or methods that change an object
in-place should return None to make it clear to the caller that the receiver was changed,
and no new object was created. Similar behavior can be seen.

DRAWBACK: since it returns None, you can't "cascade in the fluent interface style" which is big word way of saying
you can't chain methods. See more: https://en.wikipedia.org/wiki/Fluent_interface


By default, Python sorts strings lexicographically by character code.
That means ASCII uppercase letters will come before lowercase letters,
and non-ASCII characters are unlikely to be sorted in a sensible way.
So you have to figure out how to sort unicode text as humans expect

Once a sequence is sorted, it can be very efficiently searched. 
A Binary Search algo is already provided in the bisect module of Python standard lib


https://docs.python.org/3/howto/sorting.html
Python lists have a built-in list.sort() method that modifies the list in-place. There is also a sorted() built-in function that builds a new sorted list from an iterable.

>>> sorted([5, 2, 3, 1, 4])
[1, 2, 3, 4, 5]

You can also use the list.sort() method. 
It modifies the list in-place (and returns None to avoid confusion). 
Usually it’s less convenient than sorted() - but if you don’t need the original list, it’s slightly more efficient.

>>> a = [5, 2, 3, 1, 4]
>>> a.sort()
>>> a
[1, 2, 3, 4, 5]

Another difference is that the list.sort() method is 
only defined for lists. In contrast, the sorted() function accepts any iterable.

>>> sorted({1: 'D', 2: 'B', 3: 'B', 4: 'E', 5: 'A'})
[1, 2, 3, 4, 5]

KEY FUNCTIONS
key param specifies a function (or other callable) to be called on each list element

>>> sorted("This is a test string from Eden".split(), key=str.lower)
['a', 'Eden', 'from', 'is', 'string', 'test', 'This']

A common pattern is to sort complex objects using some of the object’s indices as keys. For example:

>>> student_tuples = [
...     ('john', 'A', 15),
...     ('jane', 'B', 12),
...     ('dave', 'B', 10),
... ]
>>> sorted(student_tuples, key=lambda student: student[2])   # sort by age
[('dave', 'B', 10), ('jane', 'B', 12), ('john', 'A', 15)]

The same technique works for objects with named attributes. For example:
>>> class Student:
...     def __init__(self, name, grade, age):
...         self.name = name
...         self.grade = grade
...         self.age = age
...     def __repr__(self):
...         return repr((self.name, self.grade, self.age))

>>> student_objects = [
...     Student('john', 'A', 15),
...     Student('jane', 'B', 12),
...     Student('dave', 'B', 10),
... ]
>>> sorted(student_objects, key=lambda student: student.age)   # sort by age
[('dave', 'B', 10), ('jane', 'B', 12), ('john', 'A', 15)]

The key-function pattern is common. Python has a convenience function
to make accessor functions easier and faster. 
>>> from operator import itemgetter, attrgetter

>>> sorted(student_tuples, key=itemgetter(2))
[('dave', 'B', 10), ('jane', 'B', 12), ('john', 'A', 15)]

>>> sorted(student_objects, key=attrgetter('age'))
[('dave', 'B', 10), ('jane', 'B', 12), ('john', 'A', 15)]

The operator module functions allow multiple levels of sorting. For example, to sort by grade then by age:
>>> sorted(student_tuples, key=itemgetter(1,2))
[('john', 'A', 15), ('dave', 'B', 10), ('jane', 'B', 12)]

>>> sorted(student_objects, key=attrgetter('grade', 'age'))
[('john', 'A', 15), ('dave', 'B', 10), ('jane', 'B', 12)]

Reverse Sort

>>> sorted(student_tuples, key=itemgetter(2), reverse=True)
[('john', 'A', 15), ('jane', 'B', 12), ('dave', 'B', 10)]

>>> sorted(student_objects, key=attrgetter('age'), reverse=True)
[('john', 'A', 15), ('jane', 'B', 12), ('dave', 'B', 10)]

Sort Stability and Complex Sorts
Sorts are guaranteed to be stable. 
That means that when multiple records have the same key, 
their original order is preserved.

"""


if __name__ == "__main__":
    import doctest
    doctest.testmod()