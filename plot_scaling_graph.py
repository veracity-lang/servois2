import numpy as np
import pandas as pd
import seaborn as sns
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker

def plot():
    sns.set_theme(style="whitegrid")
    d = pd.read_csv('./scaling_data.csv')
    xticks = d['#vars'].astype(str).map('\\bf{{{}}}'.format) + ' (' + d['#predicates'].astype(str) + ')'
    print(xticks)
    print(d)

    new_d = d[['#vars', 'poke', 'poke2']]
    #print(new_d)
    new_d = new_d.melt(id_vars='#vars', value_name='val', var_name='type')
    sns.lineplot(data=new_d, x='#vars', y='val', hue='type')

    plt.xticks(ticks=np.arange(2, 22, 1), labels=xticks, rotation=45)
    plt.yticks(np.arange(0,120, 20))
    plt.xlabel('#vars (#predicates)')
    plt.ylabel('time(s)')

    plt.legend(loc='center right')
    plt.subplots_adjust(bottom=0.2)
    plt.show()
    # fig.savefig('fig.png')

if __name__ == '__main__':
    plot()
