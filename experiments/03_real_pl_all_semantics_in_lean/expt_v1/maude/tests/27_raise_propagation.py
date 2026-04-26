# exception thrown inside a deep call chain
def inner():
    raise Exception("from-inner")

def middle():
    inner()

def outer():
    middle()

# uncaught propagation gets caught at top-level
try:
    outer()
except Exception as e:
    print(e)
    print("caught at top")

# loop with try-inside
total = 0
for i in range(5):
    try:
        if i == 3:
            raise Exception(i)
        total = total + i
    except Exception as v:
        print("skipped")
        print(v)
print(total)
