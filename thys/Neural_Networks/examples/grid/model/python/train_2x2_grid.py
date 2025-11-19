#! /usr/bin/env python3

# 2x2 grid: looking at verical and horzontal lines
import keras
from keras.layers import Dense
from keras.models import Sequential
import numpy as np
import tensorflowjs as tfjs
import colorama
# import vt4ai.activation
from tensorflow.keras.utils import plot_model
import tensorflow as tf
import keras.backend as K
from tensorflow.keras.utils import get_custom_objects
from keras.layers import Activation

# vt4ai.activation.init()
colorama.init()

# configuration:
EPOCHS = 10000  # 0: no training
ACTIVATION_1 = "binary_step"  # activation function for hidden layer
ACTIVATION_2 = "linear"  # activation function for output layer
SCALING = 1  # larger values make softsign approximate sign

def binary_step(x):
    return K.relu(tf.sign(x))

get_custom_objects().update({"binary_step": Activation(binary_step)})

def scale_list(s, l):
    def factor(x):
        return s * x

    return list(map(factor, l))


def scale_list_of_lists(s, ls):
    def scale(l):
        return scale_list(s, l)

    return list(map(scale, ls))


def bias_first_layer(shape, dtype=None):
    return scale_list(
        SCALING,
        [
            0.5,
            -0.5,
            -1.5,
            -2.5,
            -3.5,
            -4.5,
            -5.5,
            -6.5,
            -7.5,
            -8.5,
            -9.5,
            -10.5,
            -11.5,
            -12.5,
            -13.5,
            -14.5,
        ],
    )


def weights_first_layer(shape, dtype=None):
    return scale_list_of_lists(
        SCALING,
        [
            [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
            [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
            [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4],
            [8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8],
        ],
    )


def bias_second_layer(shape, dtype=None):
    if ACTIVATION_1 == "sigmoid" or "binary_step":
        return [1, 0, 0]
    else:  # tanh, sign, softsign
        if ACTIVATION_2 == "linear":
            return [2, 0, 0]
        else:  # relu
            return [1, -1, -1]


def weights_second_layer(shape, dtype=None):
    return [
        [0.0, 0.0, 0.0],
        [0.0, 0.0, 0.0],
        [0.0, 0.0, 0.0],
        [-1.0, 1.0, 0.0],
        [1.0, -1.0, 0.0],
        [-1.0, 0.0, 1.0],
        [1.0, 0.0, -1.0],
        [0.0, 0.0, 0.0],
        [0.0, 0.0, 0.0],
        [0.0, 0.0, 0.0],
        [-1.0, 0.0, 1.0],
        [1.0, 0.0, -1.0],
        [-1.0, 1.0, 0.0],
        [1.0, -1.0, 0.0],
        [0.0, 0.0, 0.0],
        [0.0, 0.0, 0.0],
    ]


def print_cfg(loss, accuracy, epochs, activation, activation_output, scaling):
    def print_accuracy(accuracy):
        s = "{:1.2f}".format(accuracy)
        if accuracy < 0.90:
            return colorama.Fore.RED + s + colorama.Style.RESET_ALL
        else:
            if accuracy > 0.95:
                return colorama.Fore.GREEN + s + colorama.Style.RESET_ALL
            else:
                return s

    print("Configuration:")
    print("  * Hidden Layer:")
    print("    * Activation:             ", activation)
    print("    * Scaling:                ", scaling)
    print("  * Output Layer:")
    print("    * Activation:             ", activation_output)
    print("  * Training:")
    print("    * epochs:                 ", epochs)
    print("  * Evaluation:")
    print("    * Accuracy:               ", print_accuracy(accuracy))
    print("    * Loss:                   ", loss)
    print("")


def print_predictions(xs, ys, zs):
    def str_of_real_list(col, vs):
        def hl(col, v, s):
            if v == max(vs):
                return col + s + colorama.Style.RESET_ALL
            else:
                return s

        return " ".join([hl(col, x, "{:5.2f}".format(x)) for x in vs])

    print("              Input         |    Actual Output   |   Nominal Output")
    print("    ------------------------+--------------------+-----------------")
    for x, y, z in zip(xs, ys, zs):
        if np.argmax(y) == np.argmax(z) and np.count_nonzero(y == max(y)) == 1:
            col = colorama.Fore.GREEN
        else:
            col = colorama.Fore.RED
        print(
            "    "
            + (str_of_real_list("", x))
            + " | "
            + (str_of_real_list(col, y))
            + " | "
            + (str_of_real_list(col, z))
        )
    print("")


x_precise = [
    [0.0, 0.0, 0.0, 0.0],
    [0.0, 0.0, 0.0, 1.0],
    [0.0, 0.0, 1.0, 0.0],
    [0.0, 0.0, 1.0, 1.0],
    [0.0, 1.0, 0.0, 0.0],
    [0.0, 1.0, 0.0, 1.0],
    [0.0, 1.0, 1.0, 0.0],
    [0.0, 1.0, 1.0, 1.0],
    [1.0, 0.0, 0.0, 0.0],
    [1.0, 0.0, 0.0, 1.0],
    [1.0, 0.0, 1.0, 0.0],
    [1.0, 0.0, 1.0, 1.0],
    [1.0, 1.0, 0.0, 0.0],
    [1.0, 1.0, 0.0, 1.0],
    [1.0, 1.0, 1.0, 0.0],
    [1.0, 1.0, 1.0, 1.0],
]
y_precise = [0.0, 0.0, 0.0, 1.0, 0.0, 2, 0.0, 0.0, 0.0, 0.0, 2, 0.0, 1.0, 0.0, 0.0, 0.0]

x_noisy1 = [
    [0.025, 0.025, 0.025, 0.025],
    [0.025, 0.025, 0.025, 0.975],
    [0.025, 0.025, 0.975, 0.025],
    [0.025, 0.025, 0.975, 0.975],
    [0.025, 0.975, 0.025, 0.025],
    [0.025, 0.975, 0.025, 0.975],
    [0.025, 0.975, 0.975, 0.025],
    [0.025, 0.975, 0.975, 0.975],
    [0.975, 0.025, 0.025, 0.025],
    [0.975, 0.025, 0.025, 0.975],
    [0.975, 0.025, 0.975, 0.025],
    [0.975, 0.025, 0.975, 0.975],
    [0.975, 0.975, 0.025, 0.025],
    [0.975, 0.975, 0.025, 0.975],
    [0.975, 0.975, 0.975, 0.025],
    [0.975, 0.975, 0.975, 0.975],
]
y_noisy1 = [
    0.0,
    0.0,
    0.0,
    1.0,
    0.0,
    2.0,
    0.0,
    0.0,
    0.0,
    0.0,
    2.0,
    0.0,
    1.0,
    0.0,
    0.0,
    0,
]

x_noisy2 = [
    [0.05, 0.05, 0.05, 0.05],
    [0.05, 0.05, 0.05, 0.95],
    [0.05, 0.05, 0.95, 0.05],
    [0.05, 0.05, 0.95, 0.95],
    [0.05, 0.95, 0.05, 0.05],
    [0.05, 0.95, 0.05, 0.95],
    [0.05, 0.95, 0.95, 0.05],
    [0.05, 0.95, 0.95, 0.95],
    [0.95, 0.05, 0.05, 0.05],
    [0.95, 0.05, 0.05, 0.95],
    [0.95, 0.05, 0.95, 0.05],
    [0.95, 0.05, 0.95, 0.95],
    [0.95, 0.95, 0.05, 0.05],
    [0.95, 0.95, 0.05, 0.95],
    [0.95, 0.95, 0.95, 0.05],
    [0.95, 0.95, 0.95, 0.95],
]
y_noisy2 = [
    0.0,
    0.0,
    0.0,
    1.0,
    0.0,
    2.0,
    0.0,
    0.0,
    0.0,
    0.0,
    2.0,
    0.0,
    1.0,
    0.0,
    0.0,
    0.0,
]

x_noisy3 = [
    [0.1, 0.1, 0.1, 0.1],
    [0.1, 0.1, 0.1, 0.9],
    [0.1, 0.1, 0.9, 0.1],
    [0.1, 0.1, 0.9, 0.9],
    [0.1, 0.9, 0.1, 0.1],
    [0.1, 0.9, 0.1, 0.9],
    [0.1, 0.9, 0.9, 0.1],
    [0.1, 0.9, 0.9, 0.9],
    [0.9, 0.1, 0.1, 0.1],
    [0.9, 0.1, 0.1, 0.9],
    [0.9, 0.1, 0.9, 0.1],
    [0.9, 0.1, 0.9, 0.9],
    [0.9, 0.9, 0.1, 0.1],
    [0.9, 0.9, 0.1, 0.9],
    [0.9, 0.9, 0.9, 0.1],
    [0.9, 0.9, 0.9, 0.9],
]
y_noisy3 = [
    0.0,
    0.0,
    0.0,
    1.0,
    0.0,
    2.0,
    0.0,
    0.0,
    0.0,
    0.0,
    2.0,
    0.0,
    1.0,
    0.0,
    0.0,
    0.0,
]

x_test = np.asarray(x_precise + x_noisy1 + x_noisy2 + x_noisy3, dtype="float32")
x_test_small = np.asarray(x_precise + x_noisy1, dtype="float32")

y_test = np.array(
    [
        keras.utils.to_categorical(i, num_classes=3)
        for i in y_precise + y_noisy1 + y_noisy2 + y_noisy3
    ],
    dtype="float32",
)
y_test_small = np.array(
    [
        keras.utils.to_categorical(i, num_classes=3)
        for i in y_precise + y_noisy1
    ],
    dtype="float32",
)

model = Sequential()
model.add(
    Dense(
        units=16,
        activation=ACTIVATION_1,
        kernel_initializer=weights_first_layer,
        bias_initializer=bias_first_layer,
    )
)
model.add(
    Dense(
        units=3,
        activation=ACTIVATION_2,
        kernel_initializer=weights_second_layer,
        bias_initializer=bias_second_layer,
    )
)
model.compile(
    optimizer="adam", loss="categorical_crossentropy", metrics=["binary_accuracy"]
)
history = model.fit(x_test, y_test, epochs=EPOCHS, verbose=0, validation_split=0.1)
loss, accuracy = model.evaluate(x_test, y_test, verbose=0)
predictions = model.predict(x_test)

plot_model(model, to_file="grid_nn_seq.png", show_shapes=True)

print("")
print_cfg(loss, accuracy, EPOCHS, ACTIVATION_1, ACTIVATION_2, SCALING)
print_predictions(x_test, predictions, y_test)


np.savetxt("input.txt", x_test)
np.savetxt("input_small.txt", x_test_small)
np.savetxt("expectations.txt", y_test)
np.savetxt("expectations_small.txt", y_test_small)
np.savetxt("predictions.txt", predictions)


tfjs.converters.save_keras_model(model, ".")
