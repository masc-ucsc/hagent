#!/usr/bin/env python3
"""
Cleanup script for Docker containers left over from hagent tests.

This script will stop and remove any Docker containers using hagent images
(mascucsc/hagent-* pattern), which are typically created during testing
but not cleaned up properly.
"""

import docker
import sys
import re
import os
import platform


def get_docker_client():
    """Get Docker client with fallback for different Docker setups (Colima, Docker Desktop, etc.)."""
    # First, try the standard docker.from_env()
    try:
        client = docker.from_env()
        client.ping()  # Test connection
        return client
    except Exception:
        pass  # Try alternative methods
    
    # Try platform-specific socket paths
    socket_paths = []
    system = platform.system().lower()
    username = os.getenv('USER', os.getenv('USERNAME', 'user'))
    
    if system == 'darwin':  # macOS
        socket_paths = [
            # Colima (most common alternative on macOS)
            f'/Users/{username}/.colima/default/docker.sock',
            os.path.expanduser('~/.colima/default/docker.sock'),
            # Docker Desktop paths
            f'/Users/{username}/.docker/run/docker.sock',
            os.path.expanduser('~/.docker/run/docker.sock'),
            '/var/run/docker.sock',
        ]
    elif system == 'linux':
        socket_paths = [
            '/var/run/docker.sock',
            f'/run/user/{os.getuid()}/docker.sock',
            os.path.expanduser('~/.docker/run/docker.sock'),
        ]
    else:
        socket_paths = ['/var/run/docker.sock']
    
    # Try each socket path
    for socket_path in socket_paths:
        if os.path.exists(socket_path):
            try:
                client = docker.DockerClient(base_url=f'unix://{socket_path}')
                client.ping()  # Test connection
                print(f"✅ Connected to Docker via {socket_path}")
                return client
            except Exception:
                continue
    
    return None


def cleanup_test_containers():
    """Clean up Docker containers from hagent tests."""
    try:
        # Try to connect to Docker with multiple methods
        client = get_docker_client()
        
        if client is None:
            print("❌ Cannot connect to Docker daemon")
            print("💡 Make sure Docker Desktop or Colima is running")
            print("💡 Try running: docker ps")
            return 1

        # Pattern to match hagent images: mascucsc/hagent-*
        hagent_pattern = re.compile(r'^mascucsc/hagent-.*$')

        # Find containers using hagent images
        containers = []
        for container in client.containers.list(all=True):
            image_name = container.attrs['Config']['Image']
            if hagent_pattern.match(image_name):
                containers.append(container)

        if not containers:
            print('✅ No hagent test containers found to clean up.')
            return 0

        # Group containers by image for better output
        containers_by_image = {}
        for container in containers:
            image_name = container.attrs['Config']['Image']
            if image_name not in containers_by_image:
                containers_by_image[image_name] = []
            containers_by_image[image_name].append(container)

        total_containers = len(containers)
        print(f'🧹 Found {total_containers} hagent test containers to clean up...')

        for image_name, image_containers in containers_by_image.items():
            print(f'\n📦 Image: {image_name} ({len(image_containers)} containers)')

            for container in image_containers:
                try:
                    status_msg = f'({container.status})' if container.status else ''
                    print(f'  Cleaning container {container.short_id} ({container.name}) {status_msg}...')

                    if container.status == 'running':
                        container.kill()
                    container.remove()
                    print(f'  ✅ Removed container {container.short_id}')
                except Exception as e:
                    print(f'  ❌ Failed to remove container {container.short_id}: {e}')

        print(f'\n🎉 Cleanup completed! Processed {total_containers} containers.')
        return 0

    except docker.errors.DockerException as e:
        print(f'❌ Docker error: {e}', file=sys.stderr)
        return 1
    except Exception as e:
        print(f'❌ Unexpected error: {e}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(cleanup_test_containers())
