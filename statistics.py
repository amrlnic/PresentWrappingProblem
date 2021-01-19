import os
import tqdm
import multiprocessing 
from CP.main import main as CP
from SAT.main import main as SAT
from SMT.main import main as SMT
from instance import read_instance_from_file

def get_execution_time(args):
    method_name, method, model, instance_name, instance = args
    method(instance=instance, model=model)
    stats = (instance.statistics or [ None ])[0]
    result = {
        'sat': 'false',
        'time': '-',
        'nodes': '-',
        'propagations': '-',
        'memory': '-'
    }
    if stats:
        result['sat'] = 'true'
        if method_name == 'CP':
            result['time'] =  stats['solveTime'].total_seconds()
            result['nodes'] = stats['nodes']
            result['propagations'] = stats['propagations']
            result['memory'] = stats['peakMem']
        else:
            result['time'] = stats['time']
            result['nodes'] = stats['decisions'] if 'decisions' in stats else stats['sat decisions']
            result['propagations'] = stats['propagations'] if 'propagations' in stats else (stats['sat propagations 2ary'] + stats['sat propagations nary'])
            result['memory'] = stats['max memory']
    result = { k: str(v) for k, v in result.items() }
    return method_name, model, instance_name, result

def main():
    methods = (
        ('CP', CP,  ('base_model', 'sym_model', 'rot_model', 'dup_sym_model', 'rot_sym_model', 'dup_rot_sym_model', 'base_global_model', 'rot_global_model')),
        ('SMT', SMT, ('base_model', 'sym_model', 'rot_model', 'dup_sym_model', 'rot_sym_model', 'dup_rot_sym_model')),
        ('SAT', SAT, ('base_model', 'rot_model')),
    )
    instance_files = os.listdir('instances')
    instances = [ read_instance_from_file(os.path.join('instances', file)) for file in instance_files ]
    trials = [
        (method_name, method, model, instance_file.replace('.txt', ''), instance)
        for method_name, method, models in methods
        for model in models
        for instance, instance_file in zip(instances, instance_files)
    ]
    process_num = multiprocessing.cpu_count()
    print(f'Resolving statistics with {process_num} processes')

    stats = ('sat', 'time', 'nodes', 'propagations', 'memory')

    with open('statistics.csv', 'w') as csv_output:
        csv_output.write(f'method;model;instance;{str.join(";", stats)}\n')
    
    with multiprocessing.Pool(process_num) as pool, tqdm.tqdm(initial=0, total=len(trials), desc='Solving', unit='trials') as bar:
        for method_name, model, instance_name, result in pool.imap_unordered(get_execution_time, trials):
            with open('statistics.csv', 'a') as csv_output:
                csv_output.write(f'{method_name};{model};{instance_name};{str.join(";", [ result[s] for s in stats ])}\n')
            bar.update()

if __name__ == '__main__':
    main()