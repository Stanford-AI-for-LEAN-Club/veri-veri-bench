x = ""
y = "nonempty"
if x:
    print(1)
else:
    print(2)
if y:
    print(3)
else:
    print(4)
print(x or y)
print(y or x)
print(x and y)
print(y and x)
