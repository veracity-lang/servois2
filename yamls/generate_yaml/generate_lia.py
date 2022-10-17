import sys
from jinja2 import Environment, FileSystemLoader, Template


def make_vars(var_prefix, n):
    return [var_prefix + str(i) for i in range(n)]

class LiaScaleX:
    def __init__(self, n):
        self.sizeOfX = n
        self.xVarName = 'x'
        self.X = make_vars('x', n)

    def spec_for_stateVariablesDeclaration(self):
        return '\n'.join(map((lambda v: f'- name: {v}\n  type: Int'), self.X))
    
    def spec_for_statesEqual(self):
        return ' '.join(map((lambda v: f'(= {v}_1 {v}_2)'), self.X))
        
    def spec_for_method1Ensures(self):
        return ' '.join(map((lambda v: f'(= {v}_new {v})'), self.X))
        
    def spec_for_method2Ensures(self):
        specCond = ""
        for i in range(self.sizeOfX - 1):
            xi = self.X[i]
            xj = self.X[i+1]
            specCond = specCond + (f' (> {xi} {xj})')

        specXEqual = ' '.join(map((lambda v: f'(= {v}_new {v})'), self.X))
        
        return {
            'condX': specCond,
            'xVarTerm': self.xVarName + str(self.sizeOfX -1),
            'XEqual': specXEqual
        }

    def spec_for_terms(self):
        return ", ".join(self.X)

if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    if n < 1:
        raise Exception("Minimum # of vars is 1")
        
    lia = LiaScaleX(n)
    data = {
        'Xsize': n,
        'stateXVars': lia.spec_for_stateVariablesDeclaration(),
        'stateXEqualCond': lia.spec_for_statesEqual(),
        'XinMethod1Ensures': lia.spec_for_method1Ensures(),
        'XinMethod2Ensures': lia.spec_for_method2Ensures(),
        'XTerms': lia.spec_for_terms()
    } 

    # load template
    env = Environment(loader = FileSystemLoader('./'), trim_blocks = True)
    template = env.get_template('lia_scale_var_template.j2')
    file = open(f'lia_{lia.sizeOfX}vars.yaml', 'w')
    file.write(template.render(d = data))
    file.close()
