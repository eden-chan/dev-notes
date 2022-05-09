# Unpacking 

# Parallel assignment 
"""
>>> ab = (1, 2)
>>> a,b = ab
>>> a
1
>>> b
2
>>> b, a = a, b


# Using * to grab excess items

>>> a, b, *rest = range(5)
>>> a, b, rest
(0, 1, [2, 3, 4])
>>> a, b, *rest = range(3)
>>> a, b, rest
(0, 1, [2])
>>> a, b, *rest = range(2)
>>> a, b, rest
(0, 1, [])

# Can be applied to exactly one variable, but ic an appear in any position

>>> a, *body, c, d = range(5)
>>> a, body, c, d
(0, [1, 2], 3, 4)
>>> *head, b, c, d = range(5)
>>> head, b, c, d
([0, 1], 2, 3, 4)


# Use ** (double *) for nested unpacking

"""

metro_areas = [
    ('Tokyo', 'JP', 36.933, (35.689722, 139.691667)),  
    ('Delhi NCR', 'IN', 21.935, (28.613889, 77.208889)),
    ('Mexico City', 'MX', 20.142, (19.433333, -99.133333)),
    ('New York-Newark', 'US', 20.104, (40.808611, -74.020386)),
    ('São Paulo', 'BR', 19.649, (-23.547778, -46.635833)),
]

def main():
    print(f'{"":15} | {"latitude":>9} | {"longitude":>9}')
    for name, _, _, (lat, lon) in metro_areas:  
        if lon <= 0:  
            print(f'{name:15} | {lat:9.4f} | {lon:9.4f}')

if __name__ == '__main__':
    main()


if __name__ == "__main__":
    import doctest
    doctest.testmod()
