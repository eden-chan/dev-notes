# Pre-req concepts: 
# Abstract Base Classes (ABCs) are the blueprint that represent data without implementing that data representation
# ABCs provide an interface and make sure derived concrete calsses are properly implemented
# Abstract base classes cannot be instantiated. 
# Instead, they are inherited and extended by the concrete subclasses.
# Subclasses derived from a specific abstract base class 
# must implement the methods and properties provided in that abstract base class.
# https://towardsdatascience.com/abstract-base-classes-in-python-fundamentals-for-data-scientists-3c164803224b

# Collections Collections is a built-in python module that provides useful container types. 
# They allow us to store and access values in a convenient way using data structures like 
# lists, sets, tuples, dictionary that the pythonic goats implemented with performance in mind.  
# https://towardsdatascience.com/pythons-collections-module-high-performance-container-data-types-cb4187afb5fc

# Alright, back to the book 🚀

# Python likes Collections, which are abstract base classes
# The Collection ABC (new in Python 3.6) unifies the three essential
# interfaces that every collection should implement:

# Iterable to support for, unpacking, and other forms of iteration;
# Sized to support the len built-in function;
# Container to support the in operator.

# Python does not require concrete classes to actually inherit from any of these ABCs. 
# E.g. Any class that implements __len__ satisfies the Sized interface.

# Three very important specializations of Collection are:
# Sequence, formalizing the interface of built-ins like list and str;
# Mapping, implemented by dict, collections.defaultdict, etc.;
# Set: the interface of the set and frozenset built-in types.

# Note: Since Python 3.7, the dict type is officially “ordered”,
#  but that only means that the key insertion order is preserved.
#  You cannot rearrange the keys in a dict however you like.