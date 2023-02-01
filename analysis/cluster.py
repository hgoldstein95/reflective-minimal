import os
import numpy as np
from sklearn.cluster import AffinityPropagation
import distance
import seaborn as sns

sns.set_theme()

dir = "analysis/json"
examples = []
for file in os.listdir(dir)[:10]:
    with open(dir + "/" + file, "r") as f:
        examples.append(f.read())


def check_samples(fname):
    with open(fname, "r") as f:
        samples = f.readlines()[:10]

    sns.displot(data=[len(e) for e in examples], kde=True)
    # for sample in samples:
    #     print(len(sample))
    # for sample in samples:
    #     dists = [distance.levenshtein(e, sample) for e in examples]
    #     print(np.mean(dists))


for example in examples:
    print(len(example))

print("weighted")
check_samples("analysis/weighted.json")

print("unweighted")
check_samples("analysis/unweighted.json")

# words = np.asarray(words)  #So that indexing with a list will work
# lev_similarity = -1.0 * np.array([[distance.levenshtein(w1, w2) for w1 in words] for w2 in words])

# affprop = AffinityPropagation(affinity="precomputed", damping=0.5)
# affprop.fit(lev_similarity)
# for cluster_id in np.unique(affprop.labels_):
#     exemplar = words[affprop.cluster_centers_indices_[cluster_id]]
#     cluster = np.unique(words[np.nonzero(affprop.labels_ == cluster_id)])
#     cluster_str = ", ".join(cluster)
#     print(" - *%s:* %s" % (exemplar, cluster_str))