def get_execution_time(args):
    method_name, method, model, instance_name, instance = args
    method_args = { 'instance': instance, 'model': model, 'time_limit': 7200000 }
    if method_name == 'SMT': method_args['smt_lib'] = True
    if method_name in 'SAT SMT': method_args['simple'] = True
    method(**method_args)
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

def play_beep():
    import simpleaudio as sa
    import numpy as np
    note = np.sin(880 * np.linspace(0, 0.5, 22050, False) * np.pi)
    note *= 32767 / max(note, key=abs)
    note = note.astype(np.int16)
    sa.play_buffer(note, 1, 2, 44100).wait_done()

def main():
    import os
    import tqdm
    import multiprocessing 
    import argparse
    from CP.main import main as CP
    from SAT.main import main as SAT
    from SMT.main import main as SMT
    from instance import read_instance_from_file

    parser = argparse.ArgumentParser()
    parser.add_argument('-p', '--processes', default=None, type=int, help='Number of processes to spawn')
    parser.add_argument('-o', '--output', default='statistics.csv', type=str, help='Target output file')
    parser.add_argument('-s', '--sound', nargs='?', default=False, const=True, help='True=Makes a beep each time a process ends')
    args = parser.parse_args()
    

    target_file = args.output
    stats = ('sat', 'time', 'nodes', 'propagations', 'memory')
    methods = (
        ('CP', CP,  ('base_model', 'sym_model', 'rot_model', 'dup_sym_model', 'rot_sym_model', 'dup_rot_sym_model', 'base_global_model', 'rot_global_model')),
        ('SMT', SMT, ('base_model', 'sym_model', 'rot_model', 'dup_sym_model', 'rot_sym_model', 'dup_rot_sym_model')),
        ('SAT', SAT, ('base_model', 'rot_model')),
    )
    
    already_done = []
    first = '\n'
    if os.path.exists(target_file):
        with open(target_file, 'r') as f:
            for line in (l.replace('\n', '').split(';') for l in f.readlines()[1:]):
                already_done.append(tuple(line[:3]))
    else:
        first = ''
        with open(target_file, 'w') as csv_output: csv_output.write(str.join(";", ('method', 'model', 'instance') + stats) + '\n')

    already_done = tuple(already_done)
    instance_files = os.listdir('instances')
    instances = [ read_instance_from_file(os.path.join('instances', file)) for file in instance_files ]
    trials = [
        (method_name, method, model, instance_file.replace('.txt', ''), instance)
        for method_name, method, models in methods
        for model in models
        for instance, instance_file in zip(instances, instance_files)
        if (method_name, model, instance_file.replace('.txt', '')) not in already_done
    ]
    process_num = args.processes or multiprocessing.cpu_count()
    print(f'Resolving {len(trials)} statistics with {process_num} processes')
    
    solving = [ (n, m, i) for n, _, m, i, _ in trials[:process_num] ]
    index = process_num

    def make_desc(): return 'Solving: [' + str.join(', ', [ str.join('.', s) for s in solving ]) + ']'

    with multiprocessing.Pool(process_num) as pool, tqdm.tqdm(initial=0, total=len(trials), desc=make_desc(), unit='trials') as bar:
        for method_name, model, instance_name, result in pool.imap_unordered(get_execution_time, trials):
            with open(target_file, 'a') as csv_output: csv_output.write(f'{first}{method_name};{model};{instance_name};{str.join(";", [ result[s] for s in stats ])}\n')
            first = ''

            solving.remove((method_name, model, instance_name))
            if index < len(trials):
                n, _, m, i, _ = trials[index]
                solving.append((n, m, i))
                index += 1

            bar.set_description_str(make_desc())
            bar.update()

            if args.sound: play_beep()

if __name__ == '__main__':
    main()