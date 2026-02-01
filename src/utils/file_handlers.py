import os

def get_all_smt_files_recursively(path_to_directory):
    file_paths = list()
    for r, d, f in os.walk(path_to_directory):
        for file in f:
            if ".smt20" in file:
                continue
            if ".smt2" in file:
                file_paths.append(os.path.join(r, file))

    return file_paths

def split_files(file_list, num_chunks):
    """
    Split a list of files into num_chunks.
    
    Args:
        file_list: List of files to split
        num_chunks: Number of chunks to split into
    
    Returns:
        List of lists (chunks) of files
    """
    if not file_list:
        return [[] for _ in range(num_chunks)]
    
    avg = len(file_list) / float(num_chunks)
    chunks = []
    last = 0.0
    
    while last < len(file_list):
        chunks.append(file_list[int(last):int(last + avg)])
        last += avg
        
    return chunks

def get_txt_files_list(path_to_directory):
    file_paths = list()
    for r, d, f in os.walk(path_to_directory):
        for file in f:
            if ".txt" in file:
                file_paths.append(os.path.join(r, file))
    return file_paths
