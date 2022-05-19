"""

There are classes that have fields, getting and setting methods for fields, 
and nothing else. Such classes are dumb data holders 
and are often being manipulated in far too much detail by other classes.


data class builders provide the necessary __init__, __repr__, and __eq__ methods automatically, 
None of the class builders discussed here depend on inheritance to do their work. Both collections.namedtuple and typing.NamedTuple build classes that are tuple subclasses. @dataclass is a class decorator that does not affect the class hierarchy in any way. 
Each of them uses different metaprogramming techniques to inject methods and data attributes into the class under construction.

collections.namedtuple
The simplest way—available since Python 2.6.

typing.NamedTuple
An alternative that requires type hints on the fields—since Python 3.5, 
with class syntax added in 3.6.

@dataclasses.dataclass
A class decorator that allows more customization than previous alternatives, 
adding lots of options and potential complexity—since Python 3.7.


>>> from collections import namedtuple
>>> Coordinate = namedtuple('Coordinate', 'lat lon')
>>> issubclass(Coordinate, tuple)
True
>>> moscow = Coordinate(55.756, 37.617)
>>> moscow
Coordinate(lat=55.756, lon=37.617)
>>> moscow == Coordinate(lat=55.756, lon=37.617)  
True

>>> import typing
>>> Coordinate = typing.NamedTuple('Coordinate',
...     [('lat', float), ('lon', float)])
>>> issubclass(Coordinate, tuple)
True
>>> typing.get_type_hints(Coordinate)
{'lat': <class 'float'>, 'lon': <class 'float'>}


Although NamedTuple appears in the class statement as a superclass, it’s actually not. 
typing.NamedTuple uses the advanced functionality of a metaclass2 to customize the creation
 of the user’s class. 

The collections.namedtuple function is a factory that builds subclasses of 
tuple enhanced with field names, a class name, and an informative __repr__. 
Classes built with namedtuple can be used anywhere where tuples are needed, 
and in fact many functions of the Python standard library that are used to 
return tuples now return named tuples for convenience, without affecting the user’s code at all.
Each instance of a class built by namedtuple takes exactly the same amount of memory as a tuple 
because the field names are stored in the class

>>> from collections import namedtuple
>>> City = namedtuple('City', 'name country population coordinates')  
>>> tokyo = City('Tokyo', 'JP', 36.933, (35.689722, 139.691667))  
>>> tokyo
City(name='Tokyo', country='JP', population=36.933, coordinates=(35.689722, 139.691667))
>>> tokyo.population  
36.933
>>> tokyo.coordinates
(35.689722, 139.691667)
>>> tokyo[1]
'JP'

>>> City._fields  
('name', 'country', 'population', 'coordinates')
>>> Coordinate = namedtuple('Coordinate', 'lat lon')
>>> delhi_data = ('Delhi NCR', 'IN', 21.935, Coordinate(28.613889, 77.208889))
>>> delhi = City._make(delhi_data)  # equivalent with City(*delhi_data)
>>> delhi._asdict()  
{'name': 'Delhi NCR', 'country': 'IN', 'population': 21.935, 'coordinates': Coordinate(lat=28.613889, lon=77.208889)}
>>> import json
>>> json.dumps(delhi._asdict())  
'{"name": "Delhi NCR", "country": "IN", "population": 21.935, "coordinates": [28.613889, 77.208889]}'


>>> Coordinate = namedtuple('Coordinate', 'lat lon reference name', defaults=['WGS84','origin'])
>>> Coordinate(0, 0)
Coordinate(lat=0, lon=0, reference='WGS84', name='origin')
>>> Coordinate._field_defaults
{'reference': 'WGS84', 'name': 'origin'}

type hints have no impact on the runtime behavior of Python programs
>>> import typing
>>> class Coordinate(typing.NamedTuple):
...     lat: float
...     lon: float
...
>>> trash = Coordinate('Ni!', None)
>>> print(trash)
Coordinate(lat='Ni!', lon=None)
"""

from typing import NamedTuple

class Coordinate(NamedTuple):

    """
    >>> import typing

    # >>> issubclass(Coordinate, NamedTuple)
    # False
    >>> issubclass(Coordinate, tuple)
    True
    """
    lat: float
    lon: float

    def __str__(self):
        ns = 'N' if self.lat >= 0 else 'S'
        we = 'E' if self.lon >= 0 else 'W'
        return f'{abs(self.lat):.1f}°{ns}, {abs(self.lon):.1f}°{we}'



class DemoPlainClass:
    """
    >>> DemoPlainClass.__annotations__
    {'a': <class 'int'>, 'b': <class 'float'>}

    # >>> DemoPlainClass.a
    # Traceback (most recent call last):
    # File "<stdin>", line 1, in <module>
    # AttributeError: type object 'DemoPlainClass' has no attribute 'a'
    >>> DemoPlainClass.b
    1.1
    >>> DemoPlainClass.c
    'spam'
    """
    a: int           
    b: float = 1.1   
    c = 'spam'       

from dataclasses import dataclass, field

@dataclass
class ClubMember:
    name: str
    guests: list = field(default_factory=list) # using list literal will have all instances reference the same list
    athlete: bool = field(default=False, repr=False) # omit from repr


from dataclasses import dataclass
from club import ClubMember

@dataclass
class HackerClubMember(ClubMember):                         
    """

    you may need to do more than that to initialize the instance.
    provide a __post_init__ method. 
    When that method exists, @dataclass will add code to the generated 
    __init__ to call __post_init__ as the last step.
    """
    all_handles = set()                                     
    handle: str = ''                                        

    def __post_init__(self):
        cls = self.__class__                                
        if self.handle == '':                               
            self.handle = self.name.split()[0]
        if self.handle in cls.all_handles:                  
            msg = f'handle {self.handle!r} already exists.'
            raise ValueError(msg)
        cls.all_handles.add(self.handle)                    

# bytes   dict   float   frozenset   int   list   set   str   tuple

if __name__ == "__main__":
    import doctest
    doctest.testmod()
