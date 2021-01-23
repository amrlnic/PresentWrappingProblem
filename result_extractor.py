import sys

def find(ls, filter):
    if callable(filter):
        for s in ls:
            if filter(s): return s
    else:
        for s in ls:
            if s['instance'] == filter: return s
    return None

def extract(target_file):
    with open(target_file, 'r') as f: source = [ line.replace('\n', '').split(';') for line in f.readlines()[1:] ]
    return [ { k: v.strip() for k, v in zip(statistics, row) } for row in source ]

def format_time(seconds):
    millis = int(float(seconds) * 1000)
    seconds = int(millis / 1000)
    millis -= seconds * 1000
    mins = int(seconds / 60)
    seconds -= mins * 60
    hours = int(mins / 60)
    mins -= hours * 60
    return f'{hours:02d}:{mins:02d}:{seconds:02d}.{millis:03d}'

target_file = 'statistics.csv'

methods = (
        ('CP', ('base_model', 'sym_model', 'rot_model', 'dup_sym_model', 'rot_sym_model', 'dup_rot_sym_model', 'base_global_model', 'rot_global_model')),
        ('SMT', ('base_model', 'sym_model', 'rot_model', 'dup_sym_model', 'rot_sym_model', 'dup_rot_sym_model')),
        ('SAT', ('base_model', 'rot_model')),
    )

statistics = ('method', 'model', 'instance', 'sat', 'time', 'nodes', 'propagations', 'memory')
instances = tuple([ f'{i}x{i}' for i in range(8, 41) ] + [ 'rotation_test' ])

if len(sys.argv) > 1:
    def make_table(method, model):
        method, model = method.lower(), model.lower()
        method_ref = find(methods, lambda m: m[0].lower() == method)
        if not method_ref: raise Exception(f'Method \'{method}\' not found!')
        if model not in method_ref[1]: raise Exception(f'Model \'{model}\' not found!')

        print(f'=== RUNNING: {method.upper()} - {model} ===\n')

        stats = [ s for s in extract(target_file) if s['method'].lower() == method and s['model'] == model ]

        special_name = ''
        if 'global' in model:
            if 'base' in model: special_name = ' Base Model'
            else: special_name = ' Rotation Model'
        
        with_mem = method != 'cp'
        text_bf_mem = '& \\textbf{Memory \\textit{[KB]}} ' if with_mem else ''
        table = f'''
\\begin{{center}}
    \\begin{{tabular}}{{|c|c|r|r|{'r|' if with_mem else ''}}}
        \\hline
        \\multicolumn{{{5 if with_mem else 4}}}{{|c|}}{{\\textbf{{Results{special_name}}}}} \\\\
        \\hline
        \\textbf{{Instance}} & \\textbf{{Time}} & \\textbf{{Nodes}} & \\textbf{{Propagations}} {text_bf_mem}\\\\
        
        \\hline
'''

        print('=== MISSING INSTANCES ===')
        other_column = ' & -' if with_mem else ''
        for instance in instances:
            stat = find(stats, instance)
            instance_name = instance.replace('_', '\\_')
            if stat is None:
                print(f'{method} - {model} - {instance}')
                table += f'\t\t{instance_name} & ? & ? & ?{other_column.replace("-", "?")} \\\\ \\hline\n'
            elif stat['sat'] != 'true': table += f'\t\t{instance_name} & - & - & -{other_column} \\\\ \\hline\n'
            elif float(stat['time']) < 0: table += f'\t\t{instance_name} & \\multicolumn{{{4 if with_mem else 3}}}{{|c|}}{{Time $>$ 10h - Max Time Elasped}} \\\\ \\hline\n'
            elif with_mem: table += f'\t\t{instance_name} & {format_time(stat["time"])} & {int(stat["nodes"]):,d} & {int(stat["propagations"]):,d} & {int(float(stat["memory"]) * 1000):,d} \\\\ \\hline\n'
            else: table += f'\t\t{instance_name} & {format_time(stat["time"])} & {int(stat["nodes"]):,d} & {int(stat["propagations"]):,d} \\\\ \\hline\n'

        table += '''
    \\end{tabular}
\\end{center}
'''

        print('\n=== LATEX TABLE ===\n')
        output_file = f'report/results/{method}_{model}.tex'
        print(f'Saved at: {output_file}')

        with open(f'report/results/{method}_{model}.tex', 'w') as f: f.write(table)
    

    args = [ a.lower() for a in sys.argv[1:] ]
    targets = []
    if '*' in args:
        for method, models in methods:
            for model in models:
                targets.append((method, model))
    else:
        if 'cp' in args: method = 'cp'
        elif 'smt' in args: method = 'smt'
        elif 'sat' in args: method = 'sat'
        else: raise Exception('Missing method in argument list')

        rot = 'rot' in args or 'r' in args
        sym = 'sym' in args or 's' in args
        dup = 'dup' in args or 'd' in args
        glob = 'global' in args or 'g' in args

        model = 'model'

        if glob: model = 'global_' + model
        if sym: model = 'sym_' + model
        if rot: model = 'rot_' + model
        if dup: model = 'dup_' + model
        if not sym and not rot and not dup: model = 'base_' + model
        targets.append((method, model))
    
    for target_method, target_model in targets: make_table(target_method, target_model)
else:
    stats = extract(target_file)

    missing = []
    ordered = [ statistics ]
    recon = []
    unrec = []
    already = []
    duplicated = []

    total = 0
    for method, models in methods:
        for model in models:
            for instance in instances:
                total += 1
                stat = find(stats, lambda s: s['method'] == method and s['model'] == model and s['instance'] == instance)
                if stat is None:
                    print(f'Missing instance: {method} - {model} - {instance}')
                    missing.append((method, model, instance))
                else:
                    recon.append((method, model, instance))
                    ordered.append(tuple(stat.values())) 

    for stat in stats:
        v = tuple(stat.values())
        if v[:3] not in already: already.append(v[:3])
        else:
            print(f'Duplicated instance: {str.join(" - ", v[:3])}')
            duplicated.append(v)
        if v[:3] not in recon:
            print(f'Unrecognized instance: {str.join(" - ", v[:3])}')
            unrec.append(v)

    with open(target_file, 'w') as f: f.write(str.join('\n', [ str.join(';', o) for  o in ordered ]))

    def perc(n, cp=None): return f'{len(n):3d}\t|\t{len(n)/(total if cp is None else len(cp)):7.2%}'
    print(
f'''
=== Instances Numbers ===
Missing:        {perc(missing)}
Recognized:     {perc(recon, stats)}
Unrecognized:   {perc(unrec, stats)}
Duplicated:     {perc(duplicated, stats)}
Found:          {perc(stats)}
Total:          {total}
'''
    )