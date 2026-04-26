x = 10
x += 5
print(x)        # 15
x -= 3
print(x)        # 12
x *= 4
print(x)        # 48
x //= 5
print(x)        # 9
x %= 4
print(x)        # 1

# string augmented concat
s = "ab"
s += "cd"
print(s)        # abcd
s += "ef" * 2
print(s)        # abcdefef

# list augmented concat
xs = [1, 2]
xs += [3, 4]
print(len(xs))  # 4
print(xs[3])    # 4

# subscript augmented assign
xs[0] += 100
print(xs[0])    # 101
