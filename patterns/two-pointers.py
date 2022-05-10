
"""
>>> pair_with_targetsum([1,2,3,4,5,6],6)
[0, 5]
"""


def pair_with_targetsum(arr, target_sum):
    left_most = 0
    right_most = len(arr) - 1

    while left_most < right_most:
        sum = arr[left_most] + arr[right_most]

        if sum == target_sum:
            return [left_most, right_most]

        if sum > target_sum:
            right_most-=1
        
        if sum < target_sum:
            left_most+=1


if __name__ == "__main__":
    import doctest
    doctest.testmod()
    