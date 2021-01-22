from os import replace


if __name__ == '__main__':
    import os
    import re
    import time
    import argparse
    import importlib
    from instance import read_instance_from_file, write_instance_to_file, plot_instance_to_file

    print('================================================================')
    print('================================================================')
    print('===                 Present Wrapping Problem                 ===')
    print('===      Combinatorial Decision Making and Optimization      ===')
    print('===       Group: Nicola Amoriello, Daniele Domenichelli      ===')
    print('================================================================')
    print('================================================================')
    print('')
    
    methods = ('CP', 'SAT', 'SMT')
    arg_parser = argparse.ArgumentParser()
    arg_parser.add_argument('-m', '--method', required=True, choices=methods, type=str.upper, help='Method used to carry out the solution(s), possible: CP, SAT, SMT')
    arg_parser.add_argument('-i', '--input', action='append', default=[], help='Files or directories where to locate the problem instaces')
    arg_parser.add_argument('-o', '--output', default=None, type=str, help='Directory where to store the outputs')
    arg_parser.add_argument('-img', '--images', default=None, type=str, help='Directory where to store the image representations of the outputs')
    arg_parser.add_argument('-ni', '--no-images', nargs='?', default=False, const=True, help='Prevent the generation of the image representation')
    arg_parser.add_argument('-a', '--all-solutions', nargs='?', default=False, const=True, help='Get all the solutions for each instance of the problem')
    arg_parser.add_argument('-s', '--print-stat', nargs='?', default=False, const=True, help='Print statistics for the first solution')
    arg_parser.add_argument('-t', '--time-limit', default=None, type=str, help='Max time given for solving the instances. Can be in format /[[hh:]mm:]ss[.mil]/')
    try: args, unk = arg_parser.parse_known_args()
    except: arg_parser.print_help(), exit(1)
   
    args.method = str(args.method or '').strip().upper()
    if args.method not in methods: print(f'ERROR: The given method \'{args.method}\' is not supported!'), exit(1)
    
    if args.time_limit is not None:
        time_limits = (86400, 3600, 60, 1, 0.001)
        time_limit = re.match(r'^(\d+:(?=\d{1,2}:\d{1,2}:))?(\d{1,2}:(?=\d{1,2}:))?(\d{1,2}:)?(\d*)(\.\d{1,3})?', args.time_limit)
        if time_limit is None: args.time_limit = float(args.time_limit)
        else:
            time_limit = [ (time_limit[i] or '0').strip(':').strip('.') for i in range(1, 6) ]
            time_limit[4] = (time_limit[4] + ('0' * (3 - len(time_limit[4]))))
            args.time_limit = int(sum([ float(t.strip(':')) * ts for t, ts in zip(time_limit, time_limits) ]) * 1000)

    configuration = {}
    try:
        target_module = importlib.import_module(f'{args.method}.main')
        if hasattr(target_module, 'configuration'):
            config_parser = argparse.ArgumentParser()
            target_module.configuration(config_parser)
            try:
                configuration = vars(config_parser.parse_args(unk))
                configuration = { k: configuration[k] for  k in configuration }
            except:
                arg_parser.print_help()
                print(f'\n === METHOD {args.method} CONFIGURATION\n')
                config_parser.print_help()
                exit(1)
        if not hasattr(target_module, 'main'): raise Exception('The given method is missing the main implementation')
        resolver = target_module.main
    except Exception as e: print(f'ERROR: Error during the loading of the given method'), print(e), exit(1)

    if args.output is None: args.output = os.path.join(args.method, 'out')
    if args.images is None: args.images = os.path.join(os.path.dirname(args.output), 'images')
    if not len(args.input): args.input = [ 'instances' ]
    
    instance_files = []
    for path in args.input:
        if not os.path.exists(path): print(f'ERROR: Input file \'{path}\' does not exists!'), exit(1)
        elif os.path.isdir(path): instance_files += [ os.path.join(path, file) for file in os.listdir(path) ]
        else: instance_files.append(path)
    
    output_files = [ os.path.join(args.output, os.path.basename(file).replace('.txt', '-out.txt')) for file in instance_files ]
    images_files = [ os.path.join(args.images, os.path.basename(file).replace('.txt', '.png')) for file in instance_files ]
    
    try: instances = [ read_instance_from_file(file) for file in instance_files ]
    except Exception as e: print(f'ERROR: Error while parsing the input files'), print(e), exit(1)

    # try:
    for instance, output, image_output in zip(instances, output_files, images_files):
        print(f'Solving instance: {instance}', end='\r')
        start_time = time.time()
        resolver(instance, all_solutions=args.all_solutions, time_limit=args.time_limit, **configuration)
        print(f'{instance} --> {len(instance.solutions or [])} solution{("s" if len(instance.solutions or []) != 1 else "")} in {time.time() - start_time:0.3f}s')
        if args.print_stat and instance.statistics and len(instance.statistics):
            stats = instance.statistics[0]
            if args.method == 'CP':
                print({
                    'time': stats['solveTime'].total_seconds(),
                    'nodes': stats['nodes'],
                    'propagations': stats['propagations'],
                    'memory': stats['peakMem'],
                })
            else:
                print({
                    'time': stats['time'],
                    'nodes': stats['decisions'] if 'decisions' in stats else stats['sat decisions'],
                    'propagations': stats['propagations'] if 'propagations' in stats else (stats['sat propagations 2ary'] + stats['sat propagations nary']),
                    'memory': stats['max memory'],
                })
        write_instance_to_file(instance, output, all_solutions=args.all_solutions)
        if not args.no_images: plot_instance_to_file(instance, image_output, all_solutions=args.all_solutions)
    # except Exception as e: print(f'ERROR: Error during the execution of the given method'), print(e), exit(1)

    
     
    
