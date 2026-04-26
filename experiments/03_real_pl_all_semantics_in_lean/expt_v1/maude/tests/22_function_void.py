def greet(name):
    print("hello")
    print(name)

def greet_twice(name):
    greet(name)
    greet(name)

greet("alice")
greet_twice("bob")

def early_exit(x):
    if x > 0:
        print("positive")
        return
    print("nonpositive")

early_exit(5)
early_exit(-1)
