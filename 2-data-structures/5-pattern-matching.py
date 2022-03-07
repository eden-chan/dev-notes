# Prereq concept of pattern matching (new for python 3.10) https://docs.python.org/3.10/whatsnew/3.10.html#pep-634-structural-pattern-matching
"""
>>> warning_error()
A warning has been received.
>>> errorCode = ('error', 'deez nuts', 69)
>>> warning_error(errorCode)
An error deez nuts occurred.
"""

def http_error(status):
    match status:
        case 400:
            return "Bad request"
        case 404:
            return "Not found"
        case 418:
            return "I'm a teapot"
        case _:
            return "Something's wrong with the internet"

# point is an (x, y) tuple
def printPoint(point):
    match point:
        case (0, 0):
            print("Origin")
        case (0, y):
            print(f"Y={y}")
        case (x, 0):
            print(f"X={x}")
        case (x, y):
            print(f"X={x}, Y={y}")
        case _:
            raise ValueError("Not a point")         

#  Pattern matching with Classes
class Point:
    x: int
    y: int

def location(point):
    match point:
        case Point(x=0, y=0):
            print("Origin is the point's location.")
        case Point(x=0, y=y):
            print(f"Y={y} and the point is on the y-axis.")
        case Point(x=x, y=0):
            print(f"X={x} and the point is on the x-axis.")
        case Point():
            print("The point is located somewhere else on the plane.")
        case _:
            print("Not a point")
# Pattern matching with nested patterns
def locations(points):
    match points:
        case []:
            print("No points in the list.")
        case [Point(0, 0)]:
            print("The origin is the only point in the list.")
        case [Point(x, y)]:
            print(f"A single point {x}, {y} is in the list.")
        case [Point(0, y1), Point(0, y2)]:
            print(f"Two points on the Y axis at {y1}, {y2} are in the list.")
        case _:
            print("Something else is found in the list.")


# complex patterns and wildcards
def warning_error(test_variable=('warning',404,40)):
    match test_variable:
        case ('warning', code, 40):
            print("A warning has been received.")
        case ('error', code, _):
            print(f"An error {code} occurred.")
        # no-op (no operation occurs) if none of the cases match



# Book 

if __name__ == "__main__":
    import doctest
    doctest.testmod()
