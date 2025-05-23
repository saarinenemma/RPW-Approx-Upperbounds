# This experiment is to test the convergence rate of our PRW

import argparse
import numpy as np
import time
import ot
import matplotlib.pyplot as plt
import math
from scipy.spatial.distance import cdist, pdist

import jpype
import jpype.imports
from jpype.types import *
#print(jpype.getDefaultJVMPath())
jpype.startJVM("C:/Program Files/Java/jdk-24/bin/server/jvm.dll" , classpath=['.\LMR\optimaltransportMOD.jar'])
from optimaltransport import MappingNew
from optimaltransport import Mapping
from scipy.optimize import brentq

from utils import *


# our new approximation method
def OTP_metric(X=None, Y=None, dist=None, delta=0.1, metric_scaler=1, i=0, j=0, sqrt_cost=False,p=2):
    # delta : acceptable additive error
    # q_idx : index to get returned values
    nz = len(X)

    #intial values for guessing procedure
    alphaa = 4.0*np.max(dist)/delta
    interval =4/delta
    #p=2
    currBest=10000
    currBestSolver=0
    currtime=0
    guess=0

    #guess each value and remember the smallest estimate
    while guess<=1:
        guess+=interval
        gtSolver = MappingNew(nz, list(X), list(Y), dist, delta,p,guess)
        currBestSolver=gtSolver
        
        APinfo = np.array(gtSolver.getAPinfo())
        clean_mask = (APinfo[:,2] >= 1)
        APinfo_cleaned = APinfo[clean_mask]
        cost_AP = (APinfo_cleaned[:,4]/alphaa) * (APinfo_cleaned[:,2]/(alphaa*nz))
        
        cumCost =np.power(np.cumsum(cost_AP),1/p)
        
        cumCost *= metric_scaler
        totalCost = cumCost[-1]
        if totalCost == 0:
            normalized_cumcost = (cumCost) * 0.0
        else:
            normalized_cumcost = (cumCost)/(1.0 * totalCost)

        maxdual = APinfo_cleaned[:,4]/alphaa*metric_scaler
        final_dual = maxdual[-1]
        if final_dual == 0:
            normalized_maxdual = maxdual * 0.0
        else:
            normalized_maxdual = maxdual/final_dual

        cumFlow = np.cumsum((APinfo_cleaned[:,2]).astype(int))
        totalFlow = cumFlow[-1]
        flowProgress = (cumFlow)/(1.0 * totalFlow)

        d_cost = (1 - flowProgress) - cumCost
        d_ind_a = np.nonzero(d_cost<=0)[0][0]-1
        d_ind_b = d_ind_a + 1
        alpha = find_intersection_point(flowProgress[d_ind_a], d_cost[d_ind_a], flowProgress[d_ind_b], d_cost[d_ind_b])
        alpha_OT = cumCost[d_ind_a] + (cumCost[d_ind_b]-cumCost[d_ind_a])*(alpha-flowProgress[d_ind_a])/(flowProgress[d_ind_b]-flowProgress[d_ind_a])
        alpha = 1 - alpha

        #update if better estimate
        if(alpha<currBest):
            currBestSolver=gtSolver
            currBest=alpha
        currtime+=gtSolver.getTimeTaken()

    #using our best estimate, retreive the approximation 
    gtSolver = currBestSolver
    APinfo = np.array(gtSolver.getAPinfo())

     # Clean and process APinfo data
    clean_mask = (APinfo[:,2] >= 1)
    APinfo_cleaned = APinfo[clean_mask]

    cost_AP = (APinfo_cleaned[:,4]/alphaa) * (APinfo_cleaned[:,2]/(alphaa*nz))
    cumCost =np.power(np.cumsum(cost_AP),1/p)
    cumCost *= metric_scaler
    totalCost = cumCost[-1]
    if totalCost == 0:
        normalized_cumcost = (cumCost) * 0.0
    else:
        normalized_cumcost = (cumCost)/(1.0 * totalCost)

    maxdual = APinfo_cleaned[:,4]/alphaa*metric_scaler
    final_dual = maxdual[-1]
    if final_dual == 0:
        normalized_maxdual = maxdual * 0.0
    else:
        normalized_maxdual = maxdual/final_dual

    cumFlow = np.cumsum((APinfo_cleaned[:,2]).astype(int))
    totalFlow = cumFlow[-1]
    flowProgress = (cumFlow)/(1.0 * totalFlow)

    d_cost = (1 - flowProgress) - cumCost
    d_ind_a = np.nonzero(d_cost<=0)[0][0]-1
    d_ind_b = d_ind_a + 1
    alpha = find_intersection_point(flowProgress[d_ind_a], d_cost[d_ind_a], flowProgress[d_ind_b], d_cost[d_ind_b])
    alpha_OT = cumCost[d_ind_a] + (cumCost[d_ind_b]-cumCost[d_ind_a])*(alpha-flowProgress[d_ind_a])/(flowProgress[d_ind_b]-flowProgress[d_ind_a])
    alpha = 1 - alpha

    d_cost = (1 - flowProgress) - normalized_cumcost
    d_ind_a = np.nonzero(d_cost<=0)[0][0]-1
    d_ind_b = d_ind_a + 1
    alpha_normalized = find_intersection_point(flowProgress[d_ind_a], d_cost[d_ind_a], flowProgress[d_ind_b], d_cost[d_ind_b])
    alpha_normalized_OT = normalized_cumcost[d_ind_a] + (normalized_cumcost[d_ind_b]-normalized_cumcost[d_ind_a])*(alpha_normalized-flowProgress[d_ind_a])/(flowProgress[d_ind_b]-flowProgress[d_ind_a])
    alpha_normalized = 1 - alpha_normalized
    
    d_dual = (1 - flowProgress) - maxdual
    d_ind_a = np.nonzero(d_dual<=0)[0][0]-1
    d_ind_b = d_ind_a + 1
    beta = find_intersection_point(flowProgress[d_ind_a], d_dual[d_ind_a], flowProgress[d_ind_b], d_dual[d_ind_b])
    beta_maxdual = maxdual[d_ind_a] + (maxdual[d_ind_b]-maxdual[d_ind_a])*(beta-flowProgress[d_ind_a])/(flowProgress[d_ind_b]-flowProgress[d_ind_a])
    beta = 1 - beta

    d_dual = (1 - flowProgress) - normalized_maxdual
    d_ind_a = np.nonzero(d_dual<=0)[0][0]-1
    d_ind_b = d_ind_a + 1
    beta_normalized = find_intersection_point(flowProgress[d_ind_a], d_dual[d_ind_a], flowProgress[d_ind_b], d_dual[d_ind_b])
    beta_normalized_maxdual = normalized_maxdual[d_ind_a] + (normalized_maxdual[d_ind_b]-normalized_maxdual[d_ind_a])*(beta_normalized-flowProgress[d_ind_a])/(flowProgress[d_ind_b]-flowProgress[d_ind_a])
    beta_normalized = 1 - beta_normalized
    
    realtotalCost = np.power(gtSolver.getTotalCost(),1/p)
    # realtotalCost = gtSolver.getTotalCost()

    return alpha, alpha_OT, alpha_normalized, alpha_normalized_OT, beta, beta_maxdual, beta_normalized, beta_normalized_maxdual, realtotalCost, currtime


#previous approximation method (Code directly from Kaiyi)
def OTP_metric_OLD(X=None, Y=None, dist=None, delta=0.1, metric_scaler=1, i=0, j=0, sqrt_cost=False,p=2):
    # delta : acceptable additive error
    # q_idx : index to get returned values
    nz = len(X)
    alphaa = 4.0*np.max(dist)/delta
    gtSolver = Mapping(nz, list(X), list(Y), dist, delta)
    APinfo = np.array(gtSolver.getAPinfo())

    # Clean and process APinfo data
    clean_mask = (APinfo[:,2] >= 1)
    APinfo_cleaned = APinfo[clean_mask]

    cost_AP = (APinfo_cleaned[:,4]/alphaa) * (APinfo_cleaned[:,2]/(alphaa*nz))
    cumCost =np.power(np.cumsum(cost_AP),1/p)
    # cumCost = np.cumsum(cost_AP)/(alphaa*alphaa*nz)

    cumCost *= metric_scaler
    totalCost = cumCost[-1]
    if totalCost == 0:
        normalized_cumcost = (cumCost) * 0.0
    else:
        normalized_cumcost = (cumCost)/(1.0 * totalCost)

    maxdual = APinfo_cleaned[:,4]/alphaa*metric_scaler
    final_dual = maxdual[-1]
    if final_dual == 0:
        normalized_maxdual = maxdual * 0.0
    else:
        normalized_maxdual = maxdual/final_dual

    cumFlow = np.cumsum((APinfo_cleaned[:,2]).astype(int))
    totalFlow = cumFlow[-1]
    flowProgress = (cumFlow)/(1.0 * totalFlow)

    d_cost = (1 - flowProgress) - cumCost
    d_ind_a = np.nonzero(d_cost<=0)[0][0]-1
    d_ind_b = d_ind_a + 1
    alpha = find_intersection_point(flowProgress[d_ind_a], d_cost[d_ind_a], flowProgress[d_ind_b], d_cost[d_ind_b])
    alpha_OT = cumCost[d_ind_a] + (cumCost[d_ind_b]-cumCost[d_ind_a])*(alpha-flowProgress[d_ind_a])/(flowProgress[d_ind_b]-flowProgress[d_ind_a])
    alpha = 1 - alpha

    d_cost = (1 - flowProgress) - normalized_cumcost
    d_ind_a = np.nonzero(d_cost<=0)[0][0]-1
    d_ind_b = d_ind_a + 1
    alpha_normalized = find_intersection_point(flowProgress[d_ind_a], d_cost[d_ind_a], flowProgress[d_ind_b], d_cost[d_ind_b])
    alpha_normalized_OT = normalized_cumcost[d_ind_a] + (normalized_cumcost[d_ind_b]-normalized_cumcost[d_ind_a])*(alpha_normalized-flowProgress[d_ind_a])/(flowProgress[d_ind_b]-flowProgress[d_ind_a])
    alpha_normalized = 1 - alpha_normalized
    
    d_dual = (1 - flowProgress) - maxdual
    d_ind_a = np.nonzero(d_dual<=0)[0][0]-1
    d_ind_b = d_ind_a + 1
    beta = find_intersection_point(flowProgress[d_ind_a], d_dual[d_ind_a], flowProgress[d_ind_b], d_dual[d_ind_b])
    beta_maxdual = maxdual[d_ind_a] + (maxdual[d_ind_b]-maxdual[d_ind_a])*(beta-flowProgress[d_ind_a])/(flowProgress[d_ind_b]-flowProgress[d_ind_a])
    beta = 1 - beta

    d_dual = (1 - flowProgress) - normalized_maxdual
    d_ind_a = np.nonzero(d_dual<=0)[0][0]-1
    d_ind_b = d_ind_a + 1
    beta_normalized = find_intersection_point(flowProgress[d_ind_a], d_dual[d_ind_a], flowProgress[d_ind_b], d_dual[d_ind_b])
    beta_normalized_maxdual = normalized_maxdual[d_ind_a] + (normalized_maxdual[d_ind_b]-normalized_maxdual[d_ind_a])*(beta_normalized-flowProgress[d_ind_a])/(flowProgress[d_ind_b]-flowProgress[d_ind_a])
    beta_normalized = 1 - beta_normalized
    
    realtotalCost = np.power(gtSolver.getTotalCost(),1/p)
    # realtotalCost = gtSolver.getTotalCost()

    return alpha, alpha_OT, alpha_normalized, alpha_normalized_OT, beta, beta_maxdual, beta_normalized, beta_normalized_maxdual, realtotalCost, gtSolver.getTimeTaken()


def cell_spliting_filter_2d(X, Y, n_cells=16, p=2):
    # this function is to assign each point in X and Y to a cell in 2d space, and then compute the cell-wise cost matrix, return the mass of each cell in X and Y, and the cell-wise cost matrix
    # X: source distribution points
    # Y: target distribution points
    # n_cells: number of cells in each dimension
    # return: a, b, cost
    # a: mass of each cell in X
    # b: mass of each cell in Y
    # cost: cell-wise cost matrix
    n = len(X)
    m = len(Y)
    N = n_cells**2
    a = np.zeros(N)
    b = np.zeros(N)
    a_centers = np.zeros((N, 2))
    b_centers = np.zeros((N, 2))
    cost = np.zeros((N, N))
    # compute the cell-wise cost matrix, domain is [0, 1] x [0, 1]
    for i in range(N):
        for j in range(N):
            x1 = i // n_cells
            y1 = i % n_cells
            x2 = j // n_cells
            y2 = j % n_cells
            a_centers[i] = np.array([x1+0.5, y1+0.5])/n_cells
            b_centers[j] = np.array([x2+0.5, y2+0.5])/n_cells
            cost[i,j] = np.sum((a_centers[i]-b_centers[j])**p)
    # makes aure 0<X,Y<1 for all points, if not, shift the points to boundary   
    X = np.where(X>1, 1, X)
    X = np.where(X<0, 0, X)
    Y = np.where(Y>1, 1, Y)
    Y = np.where(Y<0, 0, Y)
    # assign mass to each cell
    for i in range(n):
        x1 = int(X[i,0]*n_cells)
        y1 = int(X[i,1]*n_cells)
        a[(x1-1)*n_cells+y1-1] += 1/n
    for i in range(m):
        x2 = int(Y[i,0]*n_cells)
        y2 = int(Y[i,1]*n_cells)
        b[(x2-1)*n_cells+y2-1] += 1/m
    return a, b, cost

def find_intersection_point(x1, y1, x2, y2):
    # x1 < x2
    # y1 > 0
    # y2 < 0
    # y = ax + b
    # find x when y = 0
    a = (y2-y1)/(x2-x1)
    b = y1 - a*x1
    x = -b/a
    return x

def find_intersection_point_p(x0, y0, x1, y1, p, k=0.1):
    # print(x0, y0, x1, y1)
    # Define linear f(x) and h(x) = f(x) - g(x)
    def f_piece(x):
        return y0 + (y1 - y0) * (x - x0) / (x1 - x0)

    def h(x):
        return f_piece(x) - (k * (1 - x)) ** p

    return brentq(h, x0, x1)  # return only x



def sample_from_combined_gaussians(mu_a, mu_b, cov, cur_sample_size):
    """
    Sampling from a combination of two Gaussian distributions.
    
    :param mu_a: Mean of the first Gaussian distribution.
    :param mu_b: Mean of the second Gaussian distribution.
    :param cov: Covariance matrix common to both Gaussian distributions.
    :param cur_sample_size: Total number of samples to draw.
    :return: Samples from the combined distribution.
    """
    # Randomly decide from which Gaussian to draw each sample (0 or 1)
    choices = np.random.randint(0, 2, size=cur_sample_size)

    # Draw samples from both distributions
    samples_a = np.random.multivariate_normal(mu_a, cov, cur_sample_size)
    samples_b = np.random.multivariate_normal(mu_b, cov, cur_sample_size)

    # Select samples based on choices
    samples = np.where(choices[:, None], samples_a, samples_b)

    return samples

nn = np.linspace(1, 4, 10)
sample_size = [int(10**i) for i in nn]
N = 10
d = [2]
ms = [0.1, 1, 10]
d_OTP_metric = np.zeros((len(sample_size), len(d), len(ms), N))
d_OTP_metricOLD = np.zeros((len(sample_size), len(d), len(ms), N))
d_emd = np.zeros((len(sample_size), len(d), N))
d_l1 = np.zeros((len(sample_size), len(d), N))
delta = .0001
dist_type = 'sqeuclidean'
rand_type = 'uniform'
mu_a_d = 0.1
mu_b_d = 0.9
cov_value = 0.0001
discrete = False
argparse = "converge_exp_N_{}_2points_p_{}_dist_{}_rand_{}_mu_{}_cov_{}_discrete_{}_ms_{}".format(N, delta, dist_type, rand_type, mu_a_d, cov_value, discrete, ms)
rerun = True

# try:
#     data = np.load('./results/converge_exp_sample_converge_rate_fix_dim_2_Wasserstein_{}.npz'.format(argparse))
#     d_OTP_metric = data['d_OTP_metric']
#     d_emd = data['d_emd']
#     sample_size = data['sample_size']
#     d = data['d']
#     ms = data['ms']
# except:
#     print('file not found, rerun')
#     rerun = True

if rerun:
    for i in range(len(sample_size)):
        for j in range(len(d)):
            mu_a = np.zeros(d[j])+mu_a_d
            mu_b = np.zeros(d[j])+mu_b_d
            cov = np.eye(d[j])*cov_value
            cur_sample_size = sample_size[i]
            for p in range(2,4,1):
                np.random#.seed(k)
                if rand_type == 'uniform':
                    X = np.random.rand(cur_sample_size, d[j])
                    Y = np.random.rand(cur_sample_size, d[j])
                # or generate data from a normal distribution, given a mean and covariance matrix in d dimensions
                elif rand_type == 'normal': 
                    X = np.random.multivariate_normal(mu_a, cov, cur_sample_size)
                    Y = np.random.multivariate_normal(mu_b, cov, cur_sample_size)
                elif rand_type == 'binormal':
                    X = sample_from_combined_gaussians(mu_a, mu_b, cov, cur_sample_size)
                    Y = sample_from_combined_gaussians(mu_a, mu_b, cov, cur_sample_size)
                elif rand_type == 'two_points':
                    a = np.ones((cur_sample_size, d[j])) * mu_a
                    b = np.ones((cur_sample_size, d[j])) * mu_b
                    choices_X = np.random.randint(0, 2, size=cur_sample_size)
                    choices_Y = np.random.randint(0, 2, size=cur_sample_size)
                    X = np.where(choices_X[:, None], a, b)
                    Y = np.where(choices_Y[:, None], a, b)

                if discrete:
                    a, b, dist = cell_spliting_filter_2d(X, Y, n_cells=4, p=2)
                    # dist = dist**2
                    d_l1[i,j,0] = np.sum(np.abs(a-b))
                else:
                    dist = cdist(X, Y, metric=dist_type)
                    a = np.ones(cur_sample_size) / cur_sample_size
                    b = np.ones(cur_sample_size) / cur_sample_size

                res_emd = ot.emd2(a, b, dist, processes=1, numItermax=100000000)
                print(res_emd)
                d_emd[i,j,0] = np.power(res_emd,1/p)
                # d_emd[i,j,k] = res_emd

                for m in range(len(ms)):
                    metric_scaler = ms[m]
                    alpha, alpha_OT, alpha_normalized, alpha_normalized_OT, beta, beta_maxdual, beta_normalized, beta_normalized_maxdual, realtotalCost,timeTaken = OTP_metric(X=a, Y=b, dist=dist, delta=delta, metric_scaler=metric_scaler, i=i, j=j, sqrt_cost=True,p=p)
                    d_OTP_metric[i,j,m,0] = alpha
                    d_OTP_time=timeTaken
                    alpha, alpha_OT, alpha_normalized, alpha_normalized_OT, beta, beta_maxdual, beta_normalized, beta_normalized_maxdual, realtotalCost,timeTaken = OTP_metric_OLD(X=a, Y=b, dist=dist, delta=delta, metric_scaler=metric_scaler, i=i, j=j, sqrt_cost=True,p=p)
                    d_OTP_metricOLD[i,j,m,0] = alpha
                    d_OTP_timeOLD=timeTaken

                print('sample size: {}, dim: {}, metric scaler: {}, emd: {}, OTP: {}, OTP Time: {}, OTPOLD: {}, OTPOLD Time: {}, p: {}'.format(cur_sample_size, d[j], metric_scaler, d_emd[i,j,0], d_OTP_metric[i,j,m,0], d_OTP_time, d_OTP_metricOLD[i,j,m,0], d_OTP_timeOLD,p))
    print('save results')
    np.savez('./results/converge_exp_sample_converge_rate_fix_dim_2_Wasserstein_{}'.format(argparse), d_OTP_metric=d_OTP_metric, d_OTP_metricOLD=d_OTP_metricOLD, d_emd=d_emd, sample_size=sample_size, d=d, ms=ms)

# plot the cost curve with error band (a shaded region), x-axis: sample size (log scale), y-axis: average distance (log scale)
fig = plt.figure()
# make figure wide enough to show all subplots
fig.set_figwidth(5)
color_codes = ['g', 'b', 'c', 'r','k','w','m', 'y']
col_i = 0
for k in range(1):#len(d)):
    ax = fig.add_subplot(1, 1,k+1) #len(d), k+1)
    # make subplots spearate enough not to overlap
    # ax.set_position([0.1+k*0.3, 0.2, 0.2, 0.6])
    ax.set_xscale('log')
    ax.set_yscale('log')
    ax.set_xlabel('Sample Size')
    ax.set_ylabel('Cost')
    for m in range(len(ms)):
        d_OTP_metric_cur = d_OTP_metric[:,k,m,:]
        y = np.mean(d_OTP_metric_cur, axis=1)
        error = np.std(d_OTP_metric_cur, axis=1)
        ax.plot(sample_size, y, label='(2,{})-RPW'.format(float(1/ms[m])), color=color_codes[col_i])
        ax.fill_between(sample_size, y-error, y+error, color=color_codes[col_i], alpha=0.2)
        print('PRW, y: {}, error: {}'.format(y, error))
        print('slope: {}'.format(np.polyfit(np.log(sample_size), np.log(y), 1)[0]))
        col_i += 1
        # # fill zeros with 1e-9 to avoid dividing by zero
        # d_emd_ = np.where(d_emd==0, 1e-9, d_emd) 
        # y = np.mean(d_OTP_metric_cur/d_emd_[:,k,:], axis=1)
        # ax.plot(sample_size, y, label='PRW/EMD, k = {}'.format(float(1/ms[m])))

    for m in range(len(ms)):
        d_OTP_metric_cur_OLD = d_OTP_metricOLD[:,k,m,:]
        y = np.mean(d_OTP_metric_cur_OLD, axis=1)
        error = np.std(d_OTP_metric_cur_OLD, axis=1)
        ax.plot(sample_size, y, label='(2,{})-RPW-OLD'.format(float(1/ms[m])), color=color_codes[col_i])
        ax.fill_between(sample_size, y-error, y+error, color=color_codes[col_i], alpha=0.2)
        print('PRW, y: {}, error: {}'.format(y, error))
        print('slope: {}'.format(np.polyfit(np.log(sample_size), np.log(y), 1)[0]))
        col_i += 1
        # # fill zeros with 1e-9 to avoid dividing by zero
        # d_emd_ = np.where(d_emd==0, 1e-9, d_emd) 
        # y = np.mean(d_OTP_metric_cur/d_emd_[:,k,:], axis=1)
        # ax.plot(sample_size, y, label='PRW/EMD, k = {}'.format(float(1/ms[m])))

    d_emd_cur = d_emd[:,k,:]
    y = np.mean(d_emd_cur, axis=1)
    error = np.std(d_emd_cur, axis=1)
    ax.plot(sample_size, y, label='2-Wasserstein', color='r')
    ax.fill_between(sample_size, y-error, y+error, color='r', alpha=0.2)
    print('2-Wasserstein, y: {}, error: {}'.format(y, error))
    print('slope: {}'.format(np.polyfit(np.log(sample_size), np.log(y), 1)[0]))

    if discrete:
        d_l1_cur = d_l1[:,k,:]
        y = np.mean(d_l1_cur, axis=1)
        error = np.std(d_l1_cur, axis=1)
        ax.plot(sample_size, y, label='TV', color='orange')
        ax.fill_between(sample_size, y-error, y+error, color='orange', alpha=0.2)
        print('TV, y: {}, error: {}'.format(y, error))
        print('slope: {}'.format(np.polyfit(np.log(sample_size), np.log(y), 1)[0]))

    ax.legend()
    # make legend small enough to fit in the figure, upper right corner
    ax.legend(loc='lower left', prop={'size': 8})

# save figure with a name that contains all the parameters, so that we can compare different experiments
fig.savefig('./results/converge_exp_sample_converge_rate_fix_dim_2_Wasserstein_{}.png'.format(argparse), dpi=fig.dpi, transparent=True)
