try:
    raise Exception("boom")
    print("never")
except Exception as e:
    print("caught")
    print(e)

print("after")

# raise inside a function, caught at call site
def explode():
    raise Exception(42)

try:
    explode()
    print("not reached")
except Exception as err:
    print(err)
    print("done")
