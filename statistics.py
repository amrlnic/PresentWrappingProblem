import os
import tqdm
import time
import multiprocessing 
from CP.main import main as CP
from SAT.main import main as SAT
from SMT.main import main as SMT
from instance import read_instance_from_file

tirals_left = 0

def get_execution_time(args):
    method_name, method, model, instance_name, instance = args
    start_time = time.time()
    method(instance=instance, model=model)
    result = time.time() - start_time
    return method_name, model, instance_name, result

def main():
    methods = (
        ('CP', CP,  ('base_model', 'sym_model', 'rot_model', 'duple_sym_model', 'rot_sym_model', 'duple_rot_sym_model')),
        ('SAT', SAT, tuple()),
        ('SMT', SMT, ('base_model', 'sym_model', 'rot_model', 'duple_sym_model', 'rot_sym_model', 'duple_rot_sym_model'))
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

    with open('statistics.csv', 'w') as csv_output:
        csv_output.write('method;model;instance;elasped\n')
    
    with multiprocessing.Pool(process_num) as pool, tqdm.tqdm(initial=0, total=len(trials), desc='Solving', unit='trials') as bar:
        for method_name, model, instance_name, result in pool.imap_unordered(get_execution_time, trials):
            with open('statistics.csv', 'a') as csv_output:
                csv_output.write(f'{method_name};{model};{instance_name};{result}\n')
            bar.update()

if __name__ == '__main__':
    main()