import time
import functools # Import for preserving function metadata

def timuh(func):
    # Use @functools.wraps to copy name, docstring, etc., from func to wrapper
    @functools.wraps(func)
    def wrapper(*args, **kwargs): # 1. Accept ALL arguments
        startTime = time.perf_counter()
        result = func(*args, **kwargs) 
        endTime = time.perf_counter()
        elapsedTime = endTime - startTime
        
        print(f" {func.__name__} took: {elapsedTime:.6f} seconds to complete")
        
        # 2. Return the stored result
        return result 
        
    return wrapper

@timuh
def foo(a, b):
    """Adds two numbers after a brief wait."""
    time.sleep(0.5)
    return a + b

# The function call now works correctly
z = foo(10, 5)

# Output is correct:
print(z)
