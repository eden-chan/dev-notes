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

"""