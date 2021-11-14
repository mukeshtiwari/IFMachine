import numpy as np

# notes from the paper:
# this paper,  we focus on predicting  
# the (mean of the) response 
# variable y at a single value of the  
# explanatory  variable x, but what 
# exactly is the p25 and p75? How do
# we define the percentile?

# Answer: we will be primarily concerned 
# with the predicted values at xnew=0.25 
# and 0.75, which for ease of notation 
# we denote as p25 and p75, respectively.
# My understanding: it means that 
# first it computers m and c, and then 
# it computes the predicted value at
# xnew=0.25 and xnew=0.75. Now assuming
# that my understanding is correct, how 
# can I turn this into a function that 
# computes m and c? 

# Some obsevations: after removing the noise, np.random.laplace(0, 4 * tau/epst), 
# from the line total_clipped_gradient = np.sum(clipped_gradients, axis = 0) + np.random.laplace(0, 4 * tau/epst), 
# I get a consistent value in the bracket of [0.23 ..] for y25 and [0.76 ..] for the p75.
# This observation is consistent with m = 1.0 and c = 0.0 (y25 = 1.0 * 0.25 + 0.0, 
# y75 = 1.0 * 0.75 + 0.0). 
# Linear Regression  [0.9999999999995837, 2.0817375552543616e-13]
# (base) ➜  federated_learning git:(differential-privacy-machine-learning) ✗ python dpgdpure.py
# [0.2376002 0.7623998]
# Linear Regression  [0.9999999999995837, 2.0817375552543616e-13]
# (base) ➜  federated_learning git:(differential-privacy-machine-learning) ✗ python dpgdpure.py
# [0.2376002 0.7623998]
# Linear Regression  [0.9999999999995837, 2.0817375552543616e-13]
# (base) ➜  federated_learning git:(differential-privacy-machine-learning) ✗ python dpgdpure.py
# [0.2376002 0.7623998]
# Linear Regression  [0.9999999999995837, 2.0817375552543616e-13]
# (base) ➜  federated_learning git:(differential-privacy-machine-learning) ✗


# differential privacy linear regression
# Comments below  are generated by Github
# Copilot and it's pretty impressive!
# x and y are the data points 
# n is the length of x and y 
# T is the number of iterations
# tau is the value to clip the gradient
# p25 and p75 are the 25th and 75th percentiles of the data
# eps is the amount of privacy we want to preserve
def DPGDPure(x, y, T, tau, p25, p75, eps):
  
  epst = eps/T
  grad_sum = 0 
  packp = np.array([p25, p75])
  iterates = np.zeros((T,2))

  for t in range(0, T):
    
    # inner loop 
    yhat = 2 * (packp[0] * (3/4 - x) + packp[1]* (x-1/4))
    # what kind of loss function is this? L = (yhat - y)^2? 
    # dL/dp25 = 2 * (yhat - y) * dyhat/dp25 (* 2 * (3/4 - x) *) 
    # dL/dp75 = 2 * (yhat - y) * dyhat/dp75 (* 2 * (x - 1/4) *)
    # I am still off by 2? 
    gradients = 2 * np.column_stack((yhat - y, yhat - y)) * np.column_stack((3/4 - x, x - 1/4))

    # print("gradient", gradients[0])
    # the gradients are clipped to avoid overshooting
    clipped_gradients = np.clip(gradients, -tau, tau)
    # comment the np.random.laplace(0, 4 * tau/epst) line to get a consistent value
    # it seems that the noise is too much to get a good prediction.
    # Future research: find out some literature and see how does 
    # it prove the differential privacy guarantee, especially in
    # machine learning. 
    # Are we adding too much noise? 
    # So decreasing the clipping value to 1 and increasing the budget 
    # improves the performance.  
    total_clipped_gradient = np.sum(clipped_gradients, axis = 0) + np.random.laplace(0, 4 * tau/epst)
    grad_sum = grad_sum + (total_clipped_gradient * total_clipped_gradient)
    gamma_t = 1.0/np.sqrt(grad_sum)
    packp = packp - gamma_t * total_clipped_gradient
    iterates[t,:] = packp 

  return np.average(iterates[int(np.floor(T/2)):,:], axis=0)


# computes the m and c using the DPGDPure 
# This one appears more numerically stable
# than the linear_regression_gradient_descent, 
# defined below (comment the noise part in the
# DPGDPure function)
def compute_m_and_c(x, y, T, tau, p25, p75, eps):

  ret = DPGDPure(x, y, T, tau, p25, p75, eps);
  m = 2 * (ret[1] - ret[0])
  c = (ret[1] - m * 0.75)
  return (m, c)


# Now this works like charm. Moreover, it converges
# much faster than the linear_regression_gradient_descent
def DPGDPure_m_and_c(x, y, T, tau, m, c, eps):
  epst = eps/T
  grad_sum = 0 
  packp = np.array([m, c]) 
  iterates = np.zeros((T,2))
  n = len(x)
  for t in range(0, T):
    
    yhat = packp[0] * x + packp[1]

    #yhat = m * x + c
    #mean of sum of squared error
    #L = (yhat - y) ^ 2
    #dL/dm = 2 * (yhat - y) * x (dyhat/dm)
    #dL/dc = 2 * (yhat - y) * 1 (dyhat/dc)

    #yhat = m * x + c
    #dyhat/dm = m
    #dyhat/dc = 1
    gradients = 2.0 * np.column_stack((yhat - y, yhat - y)) * np.column_stack((x, np.full(n, 1.0)))
    clipped_gradients = np.clip(gradients, -tau, tau) 

    # Remove noise addition to see the actual gradient 
    total_clipped_gradient = np.sum(clipped_gradients, axis = 0) + np.random.laplace(0, 4 * tau/epst)
    grad_sum = grad_sum + (total_clipped_gradient * total_clipped_gradient)
    l = 1.0/np.sqrt(grad_sum)

    packp = packp - l * total_clipped_gradient
    iterates[t,:] = packp 

  return np.average(iterates[int(np.floor(T/2)):,:], axis=0)

  




# linear regression using gradient descent
# X and Y are data point
# T is the number of iteration
# l is the learing rate
# tau is the clipping value
# eps is the amount of privacy we want to preserve
# m and c are the initial values. 
def linear_regression_gradient_descent(X, Y, T, l, tau, m, c, eps):
  # initialize the parameters
  n = len(X) 
  #pack m and c into a vector
  pack = np.array([m, c])
  epst = eps/T

  for t in range(T):
    #Y_pred = m * X + c
    Y_pred = pack[0] * X + pack[1]
    # loss function is mean of sum of
    # squared error
    
    gradient = 2.0 * np.column_stack((Y_pred - Y, Y_pred - Y)) * np.column_stack((X, np.full(n, 1.0)))
    # clip the graident to avoid overshooting
    clipped_gradients = np.clip(gradient, -tau, tau) 

    # Notes: one problem is that we can't use the floating point division because
    # of timing attack. Therefore, our learning rate is constant. The problem
    # with constant learning rate is it's not converging very well, especially with 
    # noisy version. E.g., if we use this line:
    # total_clipped_gradient = (np.sum(clipped_gradients, axis = 0) + np.random.laplace(0, 4 * tau/epst))/n 
    # which corresponds to line add noise in Different Private SGD paper, https://arxiv.org/pdf/1607.00133.pdf%20.
    # If I remove the noise from the above line, the learning learning rate converges much faster. 
    # total_clipped_gradient = (np.sum(clipped_gradients, axis = 0)/n) or more succintly:
    # total_clipped_gradient = np.average(clipped_gradients, axis = 0), then you can see 
    # the gradient are much closed to the true gradient. 
    # Linear Regression using linear_regression_gradient_descent [1.00000000e+00 1.90611271e-14] (without noise).
    # (true value is m = 1.0 and c = 0.0) 

    # Todo: replay the proofs from the paper about the security proof of this implementation.
    total_clipped_gradient = np.average(clipped_gradients, axis = 0) + (np.random.laplace(0, 4 * tau/epst))/n

    pack = pack - l * total_clipped_gradient

   
  return pack 



def generate_a_line():

  # generate random data
  # line passing through (0,0) 
  # with slope of 1
  m = 1.0
  c = 0.0

  #generate random numpy array
  #x = np.array([0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9])
  # generate random numpy array
  x = np.random.uniform(0, 1, 100)
  y = m * x + c

  # increase the budget to get a better prediction
  # change 50 to 500 and see the difference
  print("DPGDPure p25 and p75", DPGDPure(x, y, 500, 1, 0.5, 0.5, 16))
  
  print("Linear Regression using linear_regression_gradient_descent", linear_regression_gradient_descent(x, y, 500, 0.01, 1, 0.5, 0.5, 16))
  print("Linear regression using (eps, 0)-DPGDP_m_and_c", DPGDPure_m_and_c(x, y, 500, 1, 0.5, 0.5, 16))
  print("Linear regression using (eps, 0)-DPGDP", compute_m_and_c(x, y, 500, 1, 0.5, 0.5, 16))


generate_a_line()

