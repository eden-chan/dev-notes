from collections import deque


class TreeNode:
    def __init__(self, val):
        self.val = val
        self.left, self.right = None, None
    def __repr__(self):
        if self == None:
            return f""
        return f"{self.val} {self.left if self.left else ''} {self.right if self.right else ''}"
def traverse(root):
    result = []
    q = deque()
    q.append(root)
    while len(q)>0:

        levelSize = len(q)
        level = []
        for _ in range(levelSize):
            x = q.popleft()
            level.append(x)
            
            if x.left:
                q.append(x.left)
            if x.right:
                q.append(x.right)
        result.append(level)   
    return result

def main():
    root = TreeNode(1)
    root.left = TreeNode(2)
    root.right = TreeNode(3)
    root.left.left = TreeNode(4)
    root.right.left = TreeNode(5)
    root.right.right = TreeNode(6)
    print("Level order traversal: " + str(traverse(root)))


main()
if __name__ == "__main__":
    import doctest
    doctest.testmod()
