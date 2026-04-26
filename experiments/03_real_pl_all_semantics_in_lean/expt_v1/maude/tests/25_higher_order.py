def apply_twice(f, x):
    return f(f(x))

def inc(n):
    return n + 1

def square(n):
    return n * n

print(apply_twice(inc, 10))     # inc(inc(10)) = 12
print(apply_twice(square, 3))   # square(square(3)) = 81

def map_list(f, xs):
    out = []
    for x in xs:
        out.append(f(x))
    return out

squares = map_list(square, [1, 2, 3, 4, 5])
print(len(squares))
print(squares[0])
print(squares[4])
