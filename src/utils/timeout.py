import signal

class TimeoutException(Exception): 
    pass 

# Define the handler function
def handler(signum, frame): 
    raise TimeoutException()

def register_timeout_handler():
    # Register the handler function
    signal.signal(signal.SIGALRM, handler)
