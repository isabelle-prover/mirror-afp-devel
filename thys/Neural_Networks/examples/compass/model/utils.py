import random
import copy
import keras
import numpy as np

NUM_CLASSES = 4

def convert_grey(li):
    l = li
    for i in range(len(l)):
        if l[i] == 0:
            l[i] = np.random.uniform(0.0, 0.2)
        else:
            l[i] = np.random.uniform(0.8, 1.0)
    return l

# X X X
# X X .
# X . X
NW = np.array([1,1,1,1,1,0,1,0,1], dtype="float32")

# X X X
# . X X
# X . X
NE = np.array([1,1,1,0,1,1,1,0,1], dtype="float32")

# X . X
# . X X
# X X X
SE = np.array([1,0,1,0,1,1,1,1,1], dtype="float32")

# X . X
# X X .
# X X X
SW = np.array([1,0,1,1,1,0,1,1,1], dtype="float32",)

x_train = np.array([NW, NE, SE, SW] * 10)
y_train = [0,1,2,3] * 10
y_train = np.array([keras.utils.np_utils.to_categorical(i, num_classes=NUM_CLASSES) for i in y_train])

x_test = np.array([convert_grey(x) for x in x_train], dtype="float32")
y_test = y_train