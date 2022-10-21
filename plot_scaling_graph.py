import numpy as np
import pandas as pd
import seaborn as sns
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker

def plot():
    # sns.set_theme(style="whitegrid")
    d = pd.read_csv('./scaling_data.csv')   
   
    new_d = d[['#predicates', 'poke', 'poke2']]
    new_d = new_d.melt(id_vars='#predicates', value_name='val', var_name='type')
    sns.lineplot(data=new_d, x='#predicates', y='val', hue='type')

    xticks = d['#predicates'].astype(str).map('{}'.format) + ' (' + d['#vars'].astype(str) + ')'
    plt.xticks(ticks=d['#predicates'], labels=xticks, rotation=315)
    plt.yticks(np.arange(0,121, 20))
    plt.xlabel('#predicates (#vars)')
    plt.ylabel('time(s)')

    plt.rcParams['figure.figsize'] = (11,6)
    plt.legend(loc='center right')
    plt.subplots_adjust(bottom=0.2)
    plt.show()

def plot_predicates_regression():
     # sns.set_theme(style="whitegrid")
    d = pd.read_csv('./scaling_data.csv')   
    sns.lmplot(data=d, x='#vars', y='#predicates')

    plt.xticks(ticks=d['#vars'], rotation=315)
    #plt.rcParams['figure.figsize'] = (11,6)
    #plt.legend(loc='center right')
    #plt.subplots_adjust(bottom=0.2)
    plt.show()

def plot_all_30vars():
    # sns.set_theme(style="whitegrid")
    d = pd.read_csv('./scalability_data_all_30v.csv')   
   
    new_d = d[['#predicates', 'simple', 'poke', 'poke2']]
    new_d = new_d.melt(id_vars='#predicates', value_name='val', var_name='type')
    sns.lineplot(data=new_d, x='#predicates', y='val', hue='type', linewidth=3)

    xticks = d['#predicates'].astype(str).map('{}'.format) + ' (' + d['#vars'].astype(str) + ')'
    plt.xticks(ticks=d['#predicates'].iloc[::3], labels=xticks.iloc[::3], fontsize=16, rotation=315)
    plt.yticks(np.arange(0,121, 20), fontsize=16)
    plt.xlabel('#predicates (#vars)', fontsize=22)
    plt.ylabel('time(s)', fontsize=22)

    #plt.rcParams.update({'font.size': 36})
    plt.rcParams['figure.figsize'] = (13,7)
    plt.legend(loc='lower right', prop={'size': 22})
    plt.subplots_adjust(bottom=0.2)    
    plt.savefig('scalability_plot.pdf')
    plt.show()

def plot_regression_vars_preds_30vars():
     # sns.set_theme(style="whitegrid")
    d = pd.read_csv('./scalability_data_all_30v.csv')   
    sns.lmplot(data=d, x='#vars', y='#predicates')

    plt.xticks(ticks=d['#vars'].iloc[::3], rotation=315)
    #plt.rcParams['figure.figsize'] = (11,6)
    #plt.legend(loc='center right')
    #plt.subplots_adjust(bottom=0.2)
    plt.show()
    #plt.savefig('vars_preds_regression.pdf')


def plot_poke2_50vars():
    # sns.set_theme(style="whitegrid")
    d = pd.read_csv('./scalability_data_poke2_50v.csv').iloc[:-12, :]   
   
    new_d = d[['#predicates', 'poke2']]
    new_d = new_d.melt(id_vars='#predicates', value_name='val', var_name='type')
    sns.lineplot(data=new_d, x='#predicates', y='val', hue='type')

    xticks = d['#predicates'].astype(str).map('{}'.format) + ' (' + d['#vars'].astype(str) + ')'
    plt.xticks(ticks=d['#predicates'].iloc[::3], labels=xticks.iloc[::3], rotation=315)
    plt.yticks(np.arange(0,121, 20))
    plt.xlabel('#predicates (#vars)')
    plt.ylabel('time(s)')

    plt.rcParams['figure.figsize'] = (11,6)
    plt.legend(loc='center right')
    plt.subplots_adjust(bottom=0.2)
    plt.show()

def plot_predicates_50vars_regression():
     # sns.set_theme(style="whitegrid")
    d = pd.read_csv('./scalability_data_poke2_50v.csv').iloc[:-12, :]   
    fig, ax = plt.subplots()
    sns.regplot(data=d, x='#vars', y='#predicates')
    ax.set_ylim(0, 3500)
    #plt.xticks(ticks=range(0,60, 5))
    #./scaling_data.csv./scaling_data.csvplt.yticks(ticks=range(0, 5500, 1000))
    #plt.rcParams['figure.figsize'] = (11,6)
    #plt.legend(loc='center right')
    #plt.subplots_adjust(bottom=0.2)
    plt.show()

if __name__ == '__main__':
    #plot()
    #plot_predicates_regression()
    #plot_poke2_50vars()
    #plot_predicates_50vars_regression()
    plot_all_30vars()
    plot_regression_vars_preds_30vars()
