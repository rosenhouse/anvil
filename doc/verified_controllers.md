## Verified Controllers

The controllers under `src/controllers/` that are verified with Anvil. Each
directory holds the controller's implementation (`exec/`), its model
(`model/`), its trusted specification (`trusted/`) and its proofs (`proof/`);
`composition/` holds the Welder specifications and the proofs that compose the
controllers. `build.md` says how to verify and run them.

- `vreplicaset_controller/`: manages the Pods of a `VReplicaSet`, a custom
  resource after the built-in ReplicaSet.
- `vdeployment_controller/`: manages the `VReplicaSet`s of a `VDeployment`,
  after the built-in Deployment.
- `vstatefulset_controller/`: manages the Pods and PersistentVolumeClaims of a
  `VStatefulSet`, after the built-in StatefulSet.
- `rabbitmq_controller/`: deploys a RabbitMQ cluster on Kubernetes for a
  `RabbitmqCluster`, after the official RabbitMQ cluster operator.
- `widget_sync_controller/`: the Widget sync controller and janitor, two
  reconcilers that run in one process in an *outer* cluster. The sync
  reconciler mirrors every `Widget` created there into an *inner* cluster and
  copies the inner copy's status back; the janitor deletes mirrors whose parent
  is gone. What is proved and what is assumed: `doc/widget_sync_design.md`.
  `deploy/widget_sync/README.md` says how to run the pair on two kind clusters.

The three built-in-workload controllers follow the
[upstream Kubernetes controllers](https://github.com/kubernetes/kubernetes/tree/master/pkg/controller);
the RabbitMQ controller follows the
[official RabbitMQ operator](https://github.com/rabbitmq/cluster-operator).
