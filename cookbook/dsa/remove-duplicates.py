"""
>>> def dedupe(items):
...    seen = set()
...    for item in items:
...        if item not in seen:
...            yield item
...            seen.add(item)

Yield is a keyword in Python that is used to return from a function
 without destroying the states of its local variable and when the 
 function is called, the execution starts from the last yield statement. 
 Any function that contains a yield keyword is termed a generator.
  Hence, yield is what makes a generator. 


>>> a = [1, 5, 2, 1, 9, 1, 5, 10]
>>> list(dedupe(a))
[1, 5, 2, 9, 10]
>>> b = dedupe(a)
# >>> b
# generator object 

https://stackoverflow.com/questions/231767/what-does-the-yield-keyword-do
When you call a function that contains a yield statement anywhere, 
you get a generator object, but no code runs. 
Then each time you extract an object from the generator, 
Python executes code in the function until it comes to a yield statement,
then pauses and delivers the object. When you extract another object, 
Python resumes just after the yield and continues until it reaches 
another yield (often the same one, but one iteration later).
This continues until the function runs off the end, at
which point the generator is deemed exhausted.


The yield keyword is reduced to two simple facts:

If the compiler detects the yield keyword anywhere inside a function, 
that function no longer returns via the return statement. 
Instead, it immediately returns a lazy "pending list" object called a generator
A generator is iterable. What is an iterable? 
It's anything like a list or set or range or dict-view, with a built-in protocol 
for visiting each element in a certain order.
In a nutshell: a generator is a lazy, incrementally-pending list, 
and yield statements allow you to use function notation to program 
the list values the generator should incrementally spit out.

"""


if __name__ == "__main__":
    import doctest
    doctest.testmod()