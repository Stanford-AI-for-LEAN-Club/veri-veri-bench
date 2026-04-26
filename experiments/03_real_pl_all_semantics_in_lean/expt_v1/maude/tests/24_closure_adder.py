def make_adder(n):
    def adder(x):
        return x + n
    return adder

add5 = make_adder(5)
add100 = make_adder(100)
print(add5(3))      # 8
print(add5(7))      # 12
print(add100(0))    # 100
print(add100(42))   # 142
