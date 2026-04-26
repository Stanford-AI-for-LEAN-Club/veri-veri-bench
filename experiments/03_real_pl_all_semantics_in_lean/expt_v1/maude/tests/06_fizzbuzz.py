i = 1
while i <= 15:
    if i % 15 == 0:
        print(-15)
    else:
        if i % 3 == 0:
            print(-3)
        else:
            if i % 5 == 0:
                print(-5)
            else:
                print(i)
    i = i + 1
