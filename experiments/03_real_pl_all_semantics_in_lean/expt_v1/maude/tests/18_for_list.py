xs = [10, 20, 30, 40, 50]
total = 0
for x in xs:
    total = total + x
print(total)

words = ["one", "two", "three"]
for w in words:
    print(w)

# nested for-loops
m = 0
for i in range(3):
    for j in range(3):
        m = m + i * j
print(m)
