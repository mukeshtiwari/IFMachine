import pandas as pd
import matplotlib.pyplot as plt
import numpy as np

# get the two columns of interest from boston data
# file. Why just two because our implementation
# of gradient descent just computes two 
# values, theta1 and theta2. 
#df = pd.read_csv("Boston_Housing_Prices.csv")
#my_col = ['crime', 'nox']
#df_new = pd.DataFrame(df[my_col])
#df_new.to_csv("crime_nox.csv", index=False, sep=' ')

# Now this works like charm. Moreover, it converges
# much faster than the linear_regression_gradient_descent,
# but it's susceptible to the floating point attack (see Alan/Toby work)
def DPGDPure_m_and_c(x, y, T, tau, m, c, eps):
  epst = eps/T
  grad_sum = 0 
  packp = np.array([m, c]) 
  iterates = np.zeros((T,2))
  n = len(x)
  for t in range(0, T):
    yhat = packp[0] * x + packp[1]
    gradients = 2.0 * np.column_stack((yhat - y, yhat - y)) * np.column_stack((x, np.full(n, 1.0)))
    clipped_gradients = np.clip(gradients, -tau, tau) 

    # Remove noise addition to see the actual gradient 
    total_clipped_gradient = np.sum(clipped_gradients, axis = 0) + np.random.laplace(0, 4 * tau/epst)
    grad_sum = grad_sum + (total_clipped_gradient * total_clipped_gradient)
    l = 1.0/np.sqrt(grad_sum)

    packp = packp - l * total_clipped_gradient
    iterates[t,:] = packp 

  return np.average(iterates[int(np.floor(T/2)):,:], axis=0)


# This one has constant time learning rate to avoid the 
# floating point attack. The downside is that it does 
# not converges as fast as the previous one 
def linear_regression_gradient_descent(X, Y, T, l, tau, m, c, eps):
  n = len(X) 
  pack = np.array([m, c])
  epst = eps/T

  for t in range(T):
    Y_pred = pack[0] * X + pack[1]
    gradient = 2.0 * np.column_stack((Y_pred - Y, Y_pred - Y)) * np.column_stack((X, np.full(n, 1.0)))
    clipped_gradients = np.clip(gradient, -tau, tau) 
    total_clipped_gradient = np.average(clipped_gradients, axis = 0) + (np.random.laplace(0, 4 * tau/epst))/n
    pack = pack - l * total_clipped_gradient

  return pack 


#computes m and c without any noise addition
def grad_linear_reg_without_noise(X, Y, T, l, tau, m, c):

  n = len(X) 
  pack = np.array([m, c])

  for t in range(T):
    Y_pred = pack[0] * X + pack[1]
    gradient = 2.0 * np.column_stack((Y_pred - Y, Y_pred - Y)) * np.column_stack((X, np.full(n, 1.0)))
    clipped_gradients = np.clip(gradient, -tau, tau) 
    total_clipped_gradient = np.average(clipped_gradients, axis = 0)
    pack = pack - l * total_clipped_gradient

  return pack 


def obsolete_method(X, Y, T, l, m, c):
  n = len(X)
  for i in range(T):
    Y_pred = m*X + c  # The current predicted value of Y
    D_m = (-2/n) * sum(X * (Y - Y_pred))  # Derivative wrt m
    D_c = (-2/n) * sum(Y - Y_pred)  # Derivative wrt c
    m = m - l * D_m  # Update m
    c = c - l * D_c  # Update c

  return [m, c]



def main():

  df = pd.read_csv("crime_nox.csv", sep=' ')
  Y = df['nox']
  X = df['crime']
  print("Linear Regression using linear_regression_gradient_descent", linear_regression_gradient_descent(X, Y, 10000, 0.01, 1, 0.5, 0.5, 16))
  print("Linear regression using (eps, 0)-DPGDP_m_and_c", DPGDPure_m_and_c(X, Y, 10000, 1, 0.5, 0.5, 16))
  print("Linear regression using grad_linear_reg_without_noise", grad_linear_reg_without_noise(X, Y, 10000, 0.1, 1, 0.5, 0.5))

if __name__ == "__main__":
    main()


#As we can see that our method is predicting a close to the actual value
#(base) ➜  federated_learning git:(differential-privacy-machine-learning) ✗ python boston_data.py
#Linear Regression using linear_regression_gradient_descent [ 0.44691069 -0.08346231]
#Linear regression using (eps, 0)-DPGDP_m_and_c [0.09030628 0.0924592 ]
#Linear regression using grad_linear_reg_without_noise [1.0527639701541383, -0.3216141713352313]

#I take my claim back. It seems that DPGDP is performing better. 
#base) ➜  federated_learning git:(differential-privacy-machine-learning) ✗ python boston_data.py
#Linear Regression using linear_regression_gradient_descent [0.15317329 0.17350816]
#Linear regression using (eps, 0)-DPGDP_m_and_c [0.31613082 0.01317968]
#Linear regression using grad_linear_reg_without_noise [1.0527639701541383, -0.3216141713352313]
#(base) ➜  federated_learning git:(differential-privacy-machine-learning) ✗ python boston_data.py
#Linear Regression using linear_regression_gradient_descent [ 0.48062984 -0.0357598 ]
#Linear regression using (eps, 0)-DPGDP_m_and_c [ 1.05973817 -0.31343437]
#Linear regression using grad_linear_reg_without_noise [1.0527639701541383, -0.3216141713352313]
#(base) ➜  federated_learning git:(differential-privacy-machine-learning) ✗ python boston_data.py
#Linear Regression using linear_regression_gradient_descent [ 0.48439637 -0.00727962]
#Linear regression using (eps, 0)-DPGDP_m_and_c [ 1.14353117 -0.36351295]
#Linear regression using grad_linear_reg_without_noise [1.0527639701541383, -0.3216141713352313]
#(base) ➜  federated_learning git:(differential-privacy-machine-learning) ✗ python boston_data.py
#Linear Regression using linear_regression_gradient_descent [0.41403652 0.0040878 ]
#Linear regression using (eps, 0)-DPGDP_m_and_c [ 0.61235082 -0.09149375]
#Linear regression using grad_linear_reg_without_noise [1.0527639701541383, -0.3216141713352313]
#(base) ➜  federated_learning git:(differential-privacy-machine-learning) ✗ python boston_data.py
#Linear Regression using linear_regression_gradient_descent [0.12460106 0.06399219]
#Linear regression using (eps, 0)-DPGDP_m_and_c [ 0.94351808 -0.2699479 ]
#Linear regression using grad_linear_reg_without_noise [1.0527639701541383, -0.3216141713352313]
#(base) ➜  federated_learning git:(differential-privacy-machine-learning) ✗


#without noise, we get this
#(base) ➜  federated_learning git:(differential-privacy-machine-learning) ✗ python boston_data.py
#Linear Regression using linear_regression_gradient_descent [ 1.98415744 -0.78144651]
#Linear regression using (eps, 0)-DPGDP_m_and_c [ 1.98472298 -0.78172444]
#Linear regression using grad_linear_reg_without_noise [1.8060443670742594, -0.6924737861083314]
#(base) ➜  federated_learning git:(differential-privacy-machine-learning) ✗