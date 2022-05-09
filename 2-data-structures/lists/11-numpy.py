"""
NumPy is why python became mainstream in scientific computing appliactions
it implements multi-dimensional, homogeneous arrays and matrix types 
that hold not only numbers but also user-defined records, 
and provides efficient elementwise operations.

NumPy is the foundation of Pandas, which implement efficient array types
that let us use nonnumeric data and provides import/export functions for
many different formats like .csv

and Scikit-learn, the currently most adopted ML tool
Most NumPy and SciPy functions are in C or C++, and leverage all CPU cores by Python's GIL (Global Interpreter Lock)
>>> import numpy as np 
>>> a = np.arange(12)  
>>> a
array([ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11])
>>> type(a)
<class 'numpy.ndarray'>
>>> a.shape  
(12,)
>>> a.shape = 3, 4  
>>> a
array([[ 0,  1,  2,  3],
       [ 4,  5,  6,  7],
       [ 8,  9, 10, 11]])
>>> a[2]  
array([ 8,  9, 10, 11])
>>> a[2, 1]  
9
>>> a[:, 1]  
array([1, 5, 9])
>>> a.transpose()  
array([[ 0,  4,  8],
       [ 1,  5,  9],
       [ 2,  6, 10],
       [ 3,  7, 11]])
"""
if __name__ == "__main__":
    import doctest
    doctest.testmod()