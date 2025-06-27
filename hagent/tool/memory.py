import chromadb
from chromadb.api.types import EmbeddingFunction
from chromadb.utils import embedding_functions

from transformers import AutoTokenizer, AutoModel

import torch
from typing import List
from dataclasses import dataclass


@dataclass
class Memory_shot:
    question: str
    answer: str


class GraphCodeBERTEmbedding(EmbeddingFunction):
    def __init__(self):
        self.tokenizer = AutoTokenizer.from_pretrained('microsoft/graphcodebert-base')
        self.model = AutoModel.from_pretrained('microsoft/graphcodebert-base')
        self.model.eval()

    def __call__(self, input: List[str]) -> List[List[float]]:
        embeddings = []
        with torch.no_grad():
            for text in input:
                tokens = self.tokenizer(text, return_tensors='pt', truncation=True, max_length=512, padding=True)
                outputs = self.model(**tokens)
                embedding = outputs.last_hidden_state[:, 0, :].squeeze().numpy()
                embeddings.append(embedding.tolist())
        return embeddings


class FewShotMemory:
    def __init__(self, learn: bool, db_path: str = './few_shot_memory_db'):
        self.db_path = db_path
        self.learn = learn
        self.client = chromadb.PersistentClient(path=db_path)

        embedding_fn = embedding_functions.SentenceTransformerEmbeddingFunction(model_name='all-MiniLM-L6-v2')

        try:
            self.collection = self.client.get_collection(
                name='code_snippets',
                embedding_function=embedding_fn,
            )
        except Exception:
            self.collection = self.client.create_collection(
                name='code_snippets',
                embedding_function=embedding_fn,
            )

    def add(self, error_type: str, fix: Memory_shot):
        if not self.learn:
            return

        snippet_id = f'snippet_{hash(error_type + fix.question)}'
        self.collection.add(
            documents=[fix.question],
            metadatas=[{'fix_question': fix.question, 'fix_answer': fix.answer, 'error_type': error_type}],
            ids=[snippet_id],
        )

    def find(self, error_type: str, fix_question: str, n_results=5) -> List[Memory_shot]:
        # Use where clause to filter by exact error_type match
        results = self.collection.query(
            query_texts=[fix_question],
            n_results=n_results,
            where={'error_type': {'$eq': error_type}},  # Exact match filter
        )
        return [
            Memory_shot(question=metadata['fix_question'], answer=metadata['fix_answer']) for metadata in results['metadatas'][0]
        ]
