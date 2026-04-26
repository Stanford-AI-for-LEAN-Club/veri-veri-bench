t = (10, 20, 30, 40)
print(t[0])
print(t[3])
print(len(t))

# tuple of strings
words = ("alpha", "beta", "gamma")
print(words[1])
print(len(words))

# truthy / falsy tuples
if ():
    print("empty truthy")
else:
    print("empty falsy")
if (1,):
    print("singleton truthy")
