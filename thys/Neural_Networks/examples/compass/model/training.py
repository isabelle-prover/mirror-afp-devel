import keras
from keras.layers import Dense
from keras.models import Sequential
import tensorflowjs as tfjs
import numpy as np
import utils

# Train the model with softmax activation on output layer for better results.
model = Sequential()
model.add(Dense(units=3, activation="linear"))
model.add(Dense(units=utils.NUM_CLASSES, activation="softmax"))
model.compile(
    optimizer="adam", loss="categorical_crossentropy", metrics=["binary_accuracy"]
)
history = model.fit(
    utils.x_train, utils.y_train, epochs=1000, verbose=2, validation_split=0.1
)


loss, accuracy = model.evaluate(utils.x_test, utils.y_test, verbose=2)
print(loss, accuracy)

predictions = model.predict(utils.x_test)
print((predictions * 100).round())

# save the weights and bias and change last layer to be linear.
weight = model.layers[1].get_weights()[0]
bias = model.layers[1].get_weights()[1]

# another hidden layer ?
test_model = Sequential()
test_model.add(model.layers[-2])
test_model.add(
    Dense(
        units=utils.NUM_CLASSES,
        activation="linear",
        kernel_initializer=keras.initializers.Constant(weight),
        bias_initializer=keras.initializers.Constant(bias),
    )
)
test_model.compile(
    optimizer="adam", loss="categorical_crossentropy", metrics=["binary_accuracy"]
)

predictions = test_model.predict(utils.x_train) 
print(f"predictions: {predictions.round()}")

predictions_grey = test_model.predict(utils.x_test) 
print(f"predictions: {predictions_grey.round()}")

loss, accuracy = test_model.evaluate(utils.x_test, utils.y_test, verbose=2)
print(loss, accuracy)

# save the inputs and model
np.savetxt("input.txt", utils.x_train)
np.savetxt("input_grey.txt", utils.x_test)
np.savetxt("predictions.txt", predictions)
np.savetxt("predictions_grey.txt", predictions_grey)
np.savetxt("expectations.txt", utils.y_train)


np.savetxt(
    "compass.txt",
    [
        utils.NW,
        utils.NE,
        utils.SE,
        utils.SW,
    ],
)

tfjs.converters.save_keras_model(test_model, ".")